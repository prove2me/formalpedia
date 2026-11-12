-- Prove2me | solution 1 for syracuse_uniform_logarithmic_tail_bound_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:43:48.475782+00:00
-- url     : https://prove2.me/submissions/5ba3a4ee-3823-4d17-860b-6179d5038475

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin
import Definitions.Def_syracuseStep
import Theorems.Thm_Tao2022Collatz_characteristic_function_le_renewal_expectation
import Theorems.Thm_Tao2022Collatz_renewal_large_black_triangle_case
import Theorems.Thm_Tao2022Collatz_renewal_white_decay_of_black_triangle_case
import Theorems.Thm_Tao2022Collatz_fine_scale_mixing_of_fourier_decay
import Theorems.Thm_Tao2022Collatz_syracuse_block_class_sum_bound
import Theorems.Thm_Tao2022Collatz_valuation_law_and_tails
import Theorems.Thm_Tao2022Collatz_section5_parameter_estimates
import Theorems.Thm_Tao2022Collatz_first_passage_stabilisation_of_mixing

set_option autoImplicit false

/-! Tao, Almost all Collatz orbits attain almost bounded values (arXiv:1909.03562v7).
Foundational layer for Theorem 3.1: the n-Syracuse valuation, the affine iterate formula
(Tao (1.5)/(1.7)) and the orbit-minimum facts used in Section 3. -/

namespace Tao31

/-- `a n = ν₂(3n+1)`, the exponent removed by one Syracuse step. -/
noncomputable def a (n : ℕ) : ℕ := (3 * n + 1).factorization 2

lemma two_pow_a_mul_step (n : ℕ) : 2 ^ a n * syracuseStep n = 3 * n + 1 := by
  unfold a syracuseStep
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/-- Partial sums `a_1 + ... + a_k` of the n-Syracuse valuation of `n`. -/
noncomputable def A (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => A n k + a (syracuseStep^[k] n)

/-- The offset `Σ_{i<k} 3^{k-1-i} 2^{A_i}`, defined recursively. -/
noncomputable def S (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * S n k + 2 ^ A n k

/-- Affine iterate formula: `2^{a_1+...+a_k} Syr^k(n) = 3^k n + S_k(n)`. -/
lemma iterate_formula (n : ℕ) (k : ℕ) :
    2 ^ A n k * syracuseStep^[k] n = 3 ^ k * n + S n k := by
  induction k with
  | zero => simp [A, S]
  | succ k ih =>
    have h := two_pow_a_mul_step (syracuseStep^[k] n)
    rw [Function.iterate_succ_apply', A, S, pow_add]
    calc 2 ^ A n k * 2 ^ a (syracuseStep^[k] n) * syracuseStep (syracuseStep^[k] n)
        = 2 ^ A n k * (3 * syracuseStep^[k] n + 1) := by rw [mul_assoc, h]
      _ = 3 * (2 ^ A n k * syracuseStep^[k] n) + 2 ^ A n k := by ring
      _ = 3 ^ (k + 1) * n + (3 * S n k + 2 ^ A n k) := by rw [ih]; ring

lemma S_eq_sum (n : ℕ) (k : ℕ) :
    S n k = ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ A n i := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [S, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]; ring
    · simp

/-! Orbit minimum facts (Section 3 uses `Syr_min(Pass) ≥ Syr_min(N)` style monotonicity). -/

lemma orbitMin_le_iterate (n k : ℕ) : syracuseOrbitMin n ≤ syracuseStep^[k] n :=
  Nat.sInf_le ⟨k, rfl⟩

lemma orbitMin_le_self (n : ℕ) : syracuseOrbitMin n ≤ n :=
  orbitMin_le_iterate n 0

lemma exists_iterate_eq_orbitMin (n : ℕ) : ∃ k, syracuseStep^[k] n = syracuseOrbitMin n :=
  Nat.sInf_mem (Set.range_nonempty (fun k : ℕ => syracuseStep^[k] n))

lemma orbitMin_le_orbitMin_iterate (n k : ℕ) :
    syracuseOrbitMin n ≤ syracuseOrbitMin (syracuseStep^[k] n) := by
  obtain ⟨j, hj⟩ := exists_iterate_eq_orbitMin (syracuseStep^[k] n)
  rw [← hj, ← Function.iterate_add_apply]
  exact orbitMin_le_iterate n (j + k)

/-- If `Syr_min(n) > M` then every orbit point exceeds `M`. -/
lemma lt_iterate_of_lt_orbitMin {n : ℕ} {M : ℝ} (h : M < (syracuseOrbitMin n : ℝ)) (k : ℕ) :
    M < (syracuseStep^[k] n : ℝ) :=
  lt_of_lt_of_le h (by exact_mod_cast orbitMin_le_iterate n k)

/-- Odd inputs give odd outputs (the step removes all factors of 2). -/
lemma step_odd (n : ℕ) : Odd (syracuseStep n) := by
  unfold syracuseStep
  have hpos : 3 * n + 1 ≠ 0 := by omega
  have := Nat.coprime_ordCompl Nat.prime_two hpos
  rw [Nat.odd_iff]
  have h2 : ¬ 2 ∣ ordCompl[2] (3 * n + 1) := Nat.not_dvd_ordCompl Nat.prime_two hpos
  omega

/-! DECOMPOSE item 2: trivial mass bound and reduction to large thresholds. -/

open Classical in
lemma mass_le_three (D E : ℕ → Prop) (x : ℝ) (hx : 2 ≤ x) :
    weightedLogMassReal D E (fun n => 1 / (n : ℝ)) x ≤ 3 := by
  unfold weightedLogMassReal
  dsimp only
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlpos : 0 < Real.log x := by linarith
  rw [div_le_iff₀ hlpos]
  have hn1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hsum : (∑ k ∈ Finset.range (⌊x⌋₊ + 1), if D k ∧ E k then 1 / (k : ℝ) else 0)
      ≤ ∑ k ∈ Finset.range ⌊x⌋₊, 1 / ((k : ℝ) + 1) := by
    rw [Finset.sum_range_succ']
    have h0 : (if D 0 ∧ E 0 then 1 / ((0 : ℕ) : ℝ) else 0) = 0 := by simp
    rw [h0, add_zero]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · push_cast; exact le_refl _
    · positivity
  have hH : ((harmonic ⌊x⌋₊ : ℚ) : ℝ) ≤ 1 + Real.log ⌊x⌋₊ := harmonic_le_one_add_log _
  have hHsum : ((harmonic ⌊x⌋₊ : ℚ) : ℝ) = ∑ k ∈ Finset.range ⌊x⌋₊, 1 / ((k : ℝ) + 1) := by
    simp [harmonic, one_div]
  have hlogn : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hnpos) hn1
  linarith

/-- It suffices to prove the bound for `M` beyond any fixed threshold `M0`. -/
lemma reduce_large_M (C0 c M0 : ℝ) (hC0 : 0 < C0) (hc : 0 < c) (hM0 : 3 ≤ M0)
    (h : ∀ M x : ℝ, M0 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C0 / Real.rpow (Real.log M) c) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 3 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C / Real.rpow (Real.log M) c := by
  refine ⟨max C0 (3 * Real.rpow (Real.log M0) c), c, lt_max_of_lt_left hC0, hc, ?_⟩
  intro M x hM hx
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hp : 0 < Real.rpow (Real.log M) c := Real.rpow_pos_of_pos hlogM c
  rcases le_or_gt M0 M with h1 | h1
  · calc _ ≤ C0 / Real.rpow (Real.log M) c := h M x h1 hx
      _ ≤ _ := by rw [div_le_div_iff_of_pos_right hp]; exact le_max_left _ _
  · have hle : Real.rpow (Real.log M) c ≤ Real.rpow (Real.log M0) c :=
      Real.rpow_le_rpow hlogM.le (Real.log_le_log (by linarith) h1.le) hc.le
    calc _ ≤ 3 := mass_le_three _ _ x hx
      _ = 3 * Real.rpow (Real.log M) c / Real.rpow (Real.log M) c := by
          rw [mul_div_assoc, div_self hp.ne', mul_one]
      _ ≤ 3 * Real.rpow (Real.log M0) c / Real.rpow (Real.log M) c := by
          rw [div_le_div_iff_of_pos_right hp]; linarith
      _ ≤ _ := by rw [div_le_div_iff_of_pos_right hp]; exact le_max_right _ _

/-! DECOMPOSE item 3: Tao Lemma 2.1 in arithmetic form. For odd `N` and a tuple `v` of
positive integers, the first `k` valuations of `N` are `v 0, ..., v (k-1)` iff
`3^k N + S_v(k) = 2^{A_v(k)} m` with `m` odd. -/

/-- Partial sums of a valuation tuple. -/
def Av (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Av v k + v k

/-- Offsets of a valuation tuple. -/
def Sv (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * Sv v k + 2 ^ Av v k

lemma AvSv_congr (v w : ℕ → ℕ) (k : ℕ) (h : ∀ i < k, v i = w i) :
    Av v k = Av w k ∧ Sv v k = Sv w k := by
  induction k with
  | zero => simp [Av, Sv]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => h i (by omega))
    have h3 := h k (by omega)
    simp only [Av, Sv, h1, h2, h3, and_self]

lemma A_S_eq (n k : ℕ) :
    A n k = Av (fun i => a (syracuseStep^[i] n)) k ∧
      S n k = Sv (fun i => a (syracuseStep^[i] n)) k := by
  induction k with
  | zero => simp [A, Av, S, Sv]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [A, Av, S, Sv, h1, h2, and_self]

lemma iterate_odd (N : ℕ) (hN : Odd N) (k : ℕ) : Odd (syracuseStep^[k] N) := by
  cases k with
  | zero => simpa using hN
  | succ k => rw [Function.iterate_succ_apply']; exact step_odd _

/-- Forward direction of Lemma 2.1. -/
lemma valuation_char_mp (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (k : ℕ)
    (h : ∀ i < k, a (syracuseStep^[i] N) = v i) :
    ∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k := by
  obtain ⟨h1, h2⟩ := AvSv_congr (fun i => a (syracuseStep^[i] N)) v k h
  obtain ⟨h3, h4⟩ := A_S_eq N k
  refine ⟨syracuseStep^[k] N, iterate_odd N hN k, ?_⟩
  rw [← h1, ← h2, ← h3, ← h4]
  exact iterate_formula N k

lemma factorization_two_pow_mul_odd (e m : ℕ) (hm : Odd m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm0 : m ≠ 0 := by obtain ⟨r, hr⟩ := hm; omega
  have hnd : ¬ 2 ∣ m := by obtain ⟨r, hr⟩ := hm; omega
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]
  simp [Nat.prime_two.factorization_self]

/-- Backward direction of Lemma 2.1 (needs every `v i ≥ 1`). -/
lemma valuation_char_mpr (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    (∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k) →
      ∀ i < k, a (syracuseStep^[i] N) = v i := by
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    rintro ⟨m, hm, hk⟩
    set P := 2 ^ Av v k with hP
    set X := 3 ^ k * N + Sv v k with hX
    have hkey : P * (2 ^ v k * m) = 3 * X + P := by
      rw [hP, hX, ← mul_assoc, ← pow_add]
      have : Av v (k + 1) = Av v k + v k := rfl
      rw [← this, hk]
      simp only [Sv, pow_succ]; ring
    have hdiv3 : P ∣ 3 * X := by
      have h1 : P ∣ 3 * X + P := ⟨_, hkey.symm⟩
      exact Nat.dvd_add_self_right.mp h1
    have hcop : Nat.Coprime P 3 := Nat.Coprime.pow_left _ (by norm_num)
    have hdivX : P ∣ X := hcop.dvd_of_dvd_mul_left hdiv3
    obtain ⟨Y, hY⟩ := hdivX
    have hPpos : 0 < P := by positivity
    have hY2 : 2 ^ v k * m = 3 * Y + 1 := by
      apply Nat.eq_of_mul_eq_mul_left hPpos
      rw [hkey, hY]; ring
    have hYodd : Odd Y := by
      obtain ⟨j, hj⟩ : ∃ j, v k = j + 1 := ⟨v k - 1, by have := hv k; omega⟩
      rw [hj, pow_succ] at hY2
      refine Nat.odd_iff.mpr ?_
      have : 2 ∣ 3 * Y + 1 := ⟨2 ^ j * m, by rw [← hY2]; ring⟩
      omega
    have hlow := ih ⟨Y, hYodd, by rw [← hY]⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact hlow i hi
    · subst hi
      obtain ⟨h1, h2⟩ := AvSv_congr (fun i => a (syracuseStep^[i] N)) v i hlow
      obtain ⟨h3, h4⟩ := A_S_eq N i
      have hf := iterate_formula N i
      rw [h3, h4, h1, h2, ← hX, hY] at hf
      have hSY : syracuseStep^[i] N = Y := Nat.eq_of_mul_eq_mul_left hPpos hf
      show (3 * syracuseStep^[i] N + 1).factorization 2 = v i
      rw [hSY, ← hY2]
      exact factorization_two_pow_mul_odd _ _ hm

/-- Tao Lemma 2.1 (arithmetic form). -/
theorem valuation_char (N : ℕ) (hN : Odd N) (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    (∀ i < k, a (syracuseStep^[i] N) = v i) ↔
      ∃ m, Odd m ∧ 2 ^ Av v k * m = 3 ^ k * N + Sv v k :=
  ⟨valuation_char_mp N hN v k, valuation_char_mpr N hN v hv k⟩

/-! DECOMPOSE item 5 setup: log-uniform odd variables `N_y`, first passage, Prop 1.11 interface. -/


/-! DECOMPOSE item 4 (Tao Section 4, Prop 1.9 with `n' = 3n`): arithmetic/counting layer. -/

lemma exists_odd_iff_mod (s X : ℕ) : (∃ m, Odd m ∧ 2 ^ s * m = X) ↔ X % 2 ^ (s + 1) = 2 ^ s := by
  constructor
  · rintro ⟨m, ⟨j, rfl⟩, rfl⟩
    have h : 2 ^ s * (2 * j + 1) = 2 ^ s + 2 ^ (s + 1) * j := by ring
    have hlt : 2 ^ s < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · intro h
    have hX := Nat.div_add_mod X (2 ^ (s + 1))
    rw [h] at hX
    refine ⟨2 * (X / 2 ^ (s + 1)) + 1, ⟨_, rfl⟩, ?_⟩
    calc 2 ^ s * (2 * (X / 2 ^ (s + 1)) + 1) = 2 ^ (s + 1) * (X / 2 ^ (s + 1)) + 2 ^ s := by ring
      _ = X := hX

lemma Av_ge (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) : k ≤ Av v k := by
  induction k with
  | zero => simp [Av]
  | succ k ih => simp only [Av]; have := hv k; omega

lemma Av_eq_sum (v : ℕ → ℕ) (k : ℕ) : Av v k = ∑ i ∈ Finset.range k, v i := by
  induction k with
  | zero => simp [Av]
  | succ k ih => rw [Av, ih, Finset.sum_range_succ]

lemma Sv_odd (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) (hk : 1 ≤ k) : Odd (Sv v k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [Sv]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [Sv, Av]
    · have h1 := ih hk1
      have h2 : Even (2 ^ Av v k) :=
        (Nat.even_pow' (by have := Av_ge v hv k; omega)).2 even_two
      exact (Odd.mul (Nat.odd_iff.2 rfl) h1).add_even h2

/-- The first `n` Syracuse valuations `a⃗^{(n)}(N)` as a tuple. -/
noncomputable def vecn (n N : ℕ) : Fin n → ℕ := fun i => a (syracuseStep^[(i : ℕ)] N)

/-- `|a⃗| = a_1 + ... + a_n`. -/
def absv {n : ℕ} (v : Fin n → ℕ) : ℕ := ∑ i, v i

/-- Pad a tuple with `1`s to a sequence. -/
def padv {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then w ⟨i, h⟩ else 1

lemma Av_padv {n : ℕ} (w : Fin n → ℕ) : Av (padv w) n = absv w := by
  rw [Av_eq_sum, absv, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => by simp [padv])

/-- Lemma 2.1 in residue form for tuples. -/
lemma vecn_eq_iff (n N : ℕ) (hN : Odd N) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) :
    vecn n N = w ↔ (3 ^ n * N + Sv (padv w) n) % 2 ^ (absv w + 1) = 2 ^ absv w := by
  have hp : ∀ i, 1 ≤ padv w i := by
    intro i; unfold padv; split_ifs <;> simp [hw]
  rw [← Av_padv w, ← exists_odd_iff_mod, ← valuation_char N hN (padv w) hp n]
  constructor
  · rintro rfl i hi
    simp [padv, hi, vecn]
  · intro h
    funext i
    have := h i i.isLt
    show a (syracuseStep^[(i : ℕ)] N) = w i
    rw [this]; simp [padv]

/-- Tuples with entries in `[1, 3n]`. -/
noncomputable def Bset (n : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc 1 (3 * n))

/-- Tuples `a⃗ ∈ (ℕ+1)^n` with `|a⃗| < 3n` (Tao's `|a⃗| < n'`, `n' = 3n`). -/
noncomputable def Tset (n : ℕ) : Finset (Fin n → ℕ) := (Bset n).filter (fun v => absv v < 3 * n)

lemma Tset_pos {n : ℕ} {w : Fin n → ℕ} (hT : w ∈ Tset n) (i : Fin n) : 1 ≤ w i := by
  have := (Finset.mem_filter.1 hT).1
  rw [Bset, Fintype.mem_piFinset] at this
  exact (Finset.mem_Icc.1 (this i)).1

lemma Tset_abs {n : ℕ} {w : Fin n → ℕ} (hT : w ∈ Tset n) : absv w + 1 ≤ 3 * n := by
  have := (Finset.mem_filter.1 hT).2; omega

lemma mod_transfer (n N N' S s : ℕ) (hs : s + 1 ≤ 3 * n) (h : N % 2 ^ (3 * n) = N' % 2 ^ (3 * n)) :
    (3 ^ n * N + S) % 2 ^ (s + 1) = (3 ^ n * N' + S) % 2 ^ (s + 1) := by
  have h1 : N ≡ N' [MOD 2 ^ (s + 1)] := Nat.ModEq.of_dvd (pow_dvd_pow 2 hs) h
  exact (h1.mul_left _).add_right _

/-- For `|a⃗| < 3n` the event `a⃗^{(n)}(N) = a⃗` depends only on `N mod 2^{3n}`. -/
lemma vecn_transfer (n N N' : ℕ) (hN : Odd N) (hN' : Odd N') (h : N % 2 ^ (3 * n) = N' % 2 ^ (3 * n))
    (hT : vecn n N ∈ Tset n) : vecn n N' = vecn n N := by
  have hw := Tset_pos hT
  rw [vecn_eq_iff n N' hN' _ hw, ← mod_transfer n N N' _ _ (Tset_abs hT) h]
  exact (vecn_eq_iff n N hN _ hw).1 rfl

lemma card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] (M q : ℕ)
    (hP : ∀ r, P (r % M) ↔ P r) :
    ((Finset.range (M * q)).filter P).card = q * ((Finset.range M).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hk : ∀ k, P (M * q + k) ↔ P k := by
      intro k
      have : (M * q + k) % M = k % M := by
        rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      rw [← hP (M * q + k), ← hP k, this]
    simp only [Nat.count_eq_card_filter_range]
    rw [Finset.filter_congr (fun k _ => hk k)]
    ring

lemma card_affine_mod (c S t M : ℕ) (hM : 0 < M) (hc : Nat.Coprime c M) (ht : t < M) :
    ((Finset.range M).filter (fun r => (c * r + S) % M = t)).card = 1 := by
  have hinj : Set.InjOn (fun r => (c * r + S) % M) (Finset.range M : Set ℕ) := by
    intro r hr r' hr' h
    simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
    have h1 : c * r + S ≡ c * r' + S [MOD M] := h
    have h2 : c * r ≡ c * r' [MOD M] := Nat.ModEq.add_right_cancel' S h1
    have h3 : r ≡ r' [MOD M] := Nat.ModEq.cancel_left_of_coprime hc.symm h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h3
  have himg : (Finset.range M).image (fun r => (c * r + S) % M) = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨r, _, rfl⟩ := hx
      exact Nat.mod_lt _ hM
    · rw [Finset.card_image_of_injOn hinj]
  have hmem : t ∈ (Finset.range M).image (fun r => (c * r + S) % M) := by
    rw [himg]; exact Finset.mem_range.2 ht
  obtain ⟨r0, hr0, hr0t⟩ := Finset.mem_image.1 hmem
  rw [Finset.card_eq_one]
  refine ⟨r0, ?_⟩
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hrt⟩
    exact hinj (Finset.mem_coe.2 (Finset.mem_range.2 hr)) (Finset.mem_coe.2 hr0)
      (hrt.trans hr0t.symm)
  · rintro rfl
    exact ⟨Finset.mem_range.1 hr0, hr0t⟩

/-- Odd residues mod `2^{3n}` (the uniform reference variable). -/
noncomputable def Rset (n : ℕ) : Finset ℕ := (Finset.range (2 ^ (3 * n))).filter Odd

lemma card_Rset (n : ℕ) (hn : 1 ≤ n) : (Rset n).card = 2 ^ (3 * n - 1) := by
  have h2 : 2 ^ (3 * n) = 2 * 2 ^ (3 * n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [Rset, h2, card_filter_range_periodic Odd 2 _ (fun r => by simp [Nat.odd_iff])]
  have : ((Finset.range 2).filter Odd).card = 1 := by decide
  rw [this, mul_one]

/-- Exact count (Tao §4): `#{r odd < 2^{3n} : a⃗^{(n)}(r) = a⃗} = 2^{3n-|a⃗|-1}` for `|a⃗| < 3n`. -/
lemma card_vecn_eq (n : ℕ) (w : Fin n → ℕ) (hT : w ∈ Tset n) :
    ((Rset n).filter (fun r => vecn n r = w)).card = 2 ^ (3 * n - (absv w + 1)) := by
  have hw := Tset_pos hT
  have hs3 := Tset_abs hT
  set s := absv w with hsdef
  set S := Sv (padv w) n with hSdef
  have hp : ∀ i, 1 ≤ padv w i := by
    intro i; unfold padv; split_ifs <;> simp [hw]
  have hsn : n ≤ s := by rw [hsdef, ← Av_padv]; exact Av_ge _ hp n
  have hn : 1 ≤ n := by omega
  have hSodd : Odd S := Sv_odd _ hp n hn
  have hodd : ∀ r, (3 ^ n * r + S) % 2 ^ (s + 1) = 2 ^ s → Odd r := by
    intro r hr
    by_contra hre
    rw [Nat.not_odd_iff_even] at hre
    have hX : Odd (3 ^ n * r + S) := (hre.mul_left _).add_odd hSodd
    have h2 : (3 ^ n * r + S) % 2 ^ (s + 1) % 2 = (3 ^ n * r + S) % 2 :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
    rw [hr, Nat.odd_iff.1 hX] at h2
    have : 2 ^ s % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    omega
  have hfilt : (Rset n).filter (fun r => vecn n r = w) =
      (Finset.range (2 ^ (3 * n))).filter (fun r => (3 ^ n * r + S) % 2 ^ (s + 1) = 2 ^ s) := by
    ext r
    simp only [Rset, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hr, ho⟩, hv⟩
      exact ⟨hr, (vecn_eq_iff n r ho w hw).1 hv⟩
    · rintro ⟨hr, hc⟩
      have ho := hodd r hc
      exact ⟨⟨hr, ho⟩, (vecn_eq_iff n r ho w hw).2 hc⟩
  have hpow : 2 ^ (3 * n) = 2 ^ (s + 1) * 2 ^ (3 * n - (s + 1)) := by
    rw [← pow_add]; congr 1; omega
  rw [hfilt, hpow, card_filter_range_periodic _ (2 ^ (s + 1)) _ (fun r => by
      rw [((Nat.mod_modEq r (2 ^ (s + 1))).mul_left (3 ^ n)).add_right S]),
    card_affine_mod (3 ^ n) S (2 ^ s) (2 ^ (s + 1)) (by positivity)
      (Nat.Coprime.pow _ _ (by norm_num)) (Nat.pow_lt_pow_right (by norm_num) (by omega)), mul_one]

/-! Geometric weights `P(Geom(2)^n = a⃗) = 2^{-|a⃗|}` on `Tset n` (Tao Lemma 2.2 tail, finite form). -/

lemma geom_sum_half (L : ℕ) : ∑ j ∈ Finset.Icc 1 L, ((1 : ℝ) / 2) ^ j = 1 - (1 / 2) ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

lemma geom_sum_34 (L : ℕ) : ∑ j ∈ Finset.Icc 1 L, ((3 : ℝ) / 4) ^ j = 3 * (1 - (3 / 4) ^ L) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

lemma sum_pi_pow (n L : ℕ) (x : ℝ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 L), x ^ absv v =
      (∑ j ∈ Finset.Icc 1 L, x ^ j) ^ n := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [absv, Finset.prod_pow_eq_pow_sum]

lemma geomT_bounds (n : ℕ) :
    1 - (n : ℝ) * (1 / 2) ^ (3 * n) - (8 / 9) ^ n ≤ ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v ∧
      ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v ≤ 1 := by
  set y : ℝ := (1 / 2) ^ (3 * n) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hB : ∑ v ∈ Bset n, ((1 : ℝ) / 2) ^ absv v = (1 - y) ^ n := by
    rw [Bset, sum_pi_pow, geom_sum_half]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Bset n) (fun v => absv v < 3 * n)
    (fun v => ((1 : ℝ) / 2) ^ absv v)
  have htail : ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v
      ≤ (8 / 9) ^ n := by
    calc _ ≤ ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n),
          ((1 : ℝ) / 2) ^ absv v * ((3 / 2) ^ absv v / (3 / 2) ^ (3 * n)) := by
            apply Finset.sum_le_sum
            intro v hv
            have h := (Finset.mem_filter.1 hv).2
            have h1 : (1 : ℝ) ≤ (3 / 2) ^ absv v / (3 / 2) ^ (3 * n) := by
              rw [le_div_iff₀ (by positivity), one_mul]
              exact pow_le_pow_right₀ (by norm_num) (by omega)
            have h0 : (0 : ℝ) ≤ (1 / 2) ^ absv v := by positivity
            nlinarith
      _ ≤ ∑ v ∈ Bset n, ((1 : ℝ) / 2) ^ absv v * ((3 / 2) ^ absv v / (3 / 2) ^ (3 * n)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
      _ = (∑ v ∈ Bset n, ((3 : ℝ) / 4) ^ absv v) / (3 / 2) ^ (3 * n) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [← mul_div_assoc, ← mul_pow]; norm_num
      _ = (3 * (1 - (3 / 4) ^ (3 * n))) ^ n / (3 / 2) ^ (3 * n) := by
            rw [Bset, sum_pi_pow, geom_sum_34]
      _ ≤ 3 ^ n / (3 / 2) ^ (3 * n) := by
            have hz0 : (0 : ℝ) ≤ (3 / 4) ^ (3 * n) := by positivity
            have hz1 : ((3 : ℝ) / 4) ^ (3 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            gcongr
            all_goals nlinarith
      _ = (8 / 9) ^ n := by rw [pow_mul, ← div_pow]; norm_num
  have hbern : 1 - (n : ℝ) * y ≤ (1 - y) ^ n := by
    calc 1 - (n : ℝ) * y = 1 + n * (-y) := by ring
      _ ≤ (1 + -y) ^ n := one_add_mul_le_pow (by linarith) n
      _ = (1 - y) ^ n := by ring
  have hle1 : (1 - y) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have htail0 : 0 ≤ ∑ v ∈ (Bset n).filter (fun v => ¬ absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hT : ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v =
      ∑ v ∈ (Bset n).filter (fun v => absv v < 3 * n), ((1 : ℝ) / 2) ^ absv v := rfl
  constructor <;> linarith


/-! Prop 1.9 assembly for a general finitely supported weight `w` on odd numbers. -/

open Classical in
/-- `P(Q(N))` for the (sub)probability weight `w` on the finite set `S`. -/
noncomputable def pm (S : Finset ℕ) (w : ℕ → ℝ) (Q : ℕ → Prop) : ℝ :=
  ∑ N ∈ S, if Q N then w N else 0

lemma pm_congr (S : Finset ℕ) (w : ℕ → ℝ) {Q Q' : ℕ → Prop} (h : ∀ N ∈ S, Q N ↔ Q' N) :
    pm S w Q = pm S w Q' := by
  unfold pm
  refine Finset.sum_congr rfl (fun N hN => ?_)
  by_cases hq : Q N
  · rw [if_pos hq, if_pos ((h N hN).1 hq)]
  · rw [if_neg hq, if_neg (fun h' => hq ((h N hN).2 h'))]

lemma pm_split (S : Finset ℕ) (w : ℕ → ℝ) (Q R : ℕ → Prop) :
    pm S w Q = pm S w (fun N => Q N ∧ R N) + pm S w (fun N => Q N ∧ ¬ R N) := by
  unfold pm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  by_cases hq : Q N <;> by_cases hr : R N <;> simp [hq, hr]

lemma pm_nonneg (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ N ∈ S, 0 ≤ w N) (Q : ℕ → Prop) :
    0 ≤ pm S w Q := by
  unfold pm
  refine Finset.sum_nonneg (fun N hN => ?_)
  split_ifs
  · exact hw N hN
  · exact le_refl _

lemma pm_mono (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ N ∈ S, 0 ≤ w N) {Q Q' : ℕ → Prop}
    (h : ∀ N ∈ S, Q N → Q' N) : pm S w Q ≤ pm S w Q' := by
  unfold pm
  refine Finset.sum_le_sum (fun N hN => ?_)
  by_cases hq : Q N
  · rw [if_pos hq, if_pos (h N hN hq)]
  · rw [if_neg hq]
    split_ifs
    · exact hw N hN
    · exact le_refl _

open Classical in
/-- Uniform odd residue mod `2^{3n}`: `P(a⃗^{(n)} = a⃗, a⃗ ∈ E ∩ T) = Σ 2^{-|a⃗|}`. -/
lemma U_vec_E (n : ℕ) (E : (Fin n → ℕ) → Prop) :
    (((Rset n).filter (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) =
      ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v := by
  rw [Finset.card_eq_sum_card_fiberwise (f := vecn n) (t := (Tset n).filter E) ?_]
  · push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvT := (Finset.mem_filter.1 hv).1
    have hfib : ((Rset n).filter (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)).filter
        (fun r => vecn n r = v) = (Rset n).filter (fun r => vecn n r = v) := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_, ?_⟩, h2⟩
        · rw [h2]; exact (Finset.mem_filter.1 hv).2
        · rw [h2]; exact hvT
    rw [hfib, card_vecn_eq n v hvT]
    have hs := Tset_abs hvT
    have : (2 : ℝ) ^ (3 * n - 1) = 2 ^ (3 * n - (absv v + 1)) * 2 ^ absv v := by
      rw [← pow_add]; congr 1; omega
    rw [this, one_div_pow]
    push_cast
    field_simp
  · intro r hr
    have := (Finset.mem_filter.1 hr).2
    exact Finset.mem_filter.2 ⟨this.2, this.1⟩

open Classical in
/-- Uniform odd residue mod `2^{3n}`: `P(|a⃗^{(n)}| ≥ 3n) ≤ n 2^{-3n} + (8/9)^n` (Lemma 4.1 at `n' = 3n`). -/
lemma U_tail (n : ℕ) (hn : 1 ≤ n) :
    (((Rset n).filter (fun r => vecn n r ∉ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) ≤
      (n : ℝ) * (1 / 2) ^ (3 * n) + (8 / 9) ^ n := by
  have hT : (((Rset n).filter (fun r => vecn n r ∈ Tset n)).card : ℝ) / 2 ^ (3 * n - 1) =
      ∑ v ∈ Tset n, ((1 : ℝ) / 2) ^ absv v := by
    have h := U_vec_E n (fun _ => True)
    convert h using 4
    all_goals (try ext)
    all_goals simp
  have hc := Finset.card_filter_add_card_filter_not (s := Rset n) (fun r => vecn n r ∈ Tset n)
  rw [card_Rset n hn] at hc
  have hc' : (((Rset n).filter (fun r => vecn n r ∉ Tset n)).card : ℝ) =
      2 ^ (3 * n - 1) - ((Rset n).filter (fun r => vecn n r ∈ Tset n)).card := by
    have : (((Rset n).filter (fun r => vecn n r ∈ Tset n)).card : ℝ) +
        ((Rset n).filter (fun r => vecn n r ∉ Tset n)).card = 2 ^ (3 * n - 1) := by
      exact_mod_cast hc
    linarith
  rw [hc', sub_div, div_self (by positivity), hT]
  linarith [(geomT_bounds n).1]

lemma small_terms (n : ℕ) :
    ((1 : ℝ) / 2) ^ (3 * n) ≤ (8 / 9) ^ n ∧ (n : ℝ) * (1 / 2) ^ (3 * n) ≤ (8 / 9) ^ n := by
  have hy : ((1 : ℝ) / 2) ^ (3 * n) = (1 / 8) ^ n := by rw [pow_mul]; norm_num
  have h2n' : n < 2 ^ n := by
    first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow n | exact n.lt_two_pow_self
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast h2n'.le
  rw [hy]
  constructor
  · exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  · calc (n : ℝ) * (1 / 8) ^ n ≤ 2 ^ n * (1 / 8) ^ n :=
          mul_le_mul_of_nonneg_right h2n (by positivity)
      _ = (1 / 4) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ (8 / 9) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n

open Classical in
/-- **Tao Proposition 1.9** (with `n' = 3n`, event form). If the weight `w` on odd numbers makes
`N mod 2^{3n}` uniform on odd residues up to `K 2^{-3n}` in every event, then the first `n`
Syracuse valuations are `Geom(2)^n`-distributed up to `(2K+2)(8/9)^n` in every event. -/
theorem prop19 (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (w : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hodd : ∀ N ∈ S, Odd N) (hw : ∀ N ∈ S, 0 ≤ w N)
    (hU : ∀ P : ℕ → Prop, |pm S w (fun N => P (N % 2 ^ (3 * n))) -
      (((Rset n).filter P).card : ℝ) / 2 ^ (3 * n - 1)| ≤ K * (1 / 2) ^ (3 * n))
    (E : (Fin n → ℕ) → Prop) :
    |pm S w (fun N => E (vecn n N)) - ∑ v ∈ (Tset n).filter E, ((1 : ℝ) / 2) ^ absv v| ≤
      (2 * K + 2) * (8 / 9) ^ n := by
  have hmododd : ∀ N ∈ S, Odd (N % 2 ^ (3 * n)) := by
    intro N hN
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
    exact Nat.odd_iff.1 (hodd N hN)
  have hTiff : ∀ N ∈ S, (vecn n N ∈ Tset n ↔ vecn n (N % 2 ^ (3 * n)) ∈ Tset n) ∧
      (vecn n N ∈ Tset n → vecn n (N % 2 ^ (3 * n)) = vecn n N) := by
    intro N hN
    have hm : N % 2 ^ (3 * n) = (N % 2 ^ (3 * n)) % 2 ^ (3 * n) := (Nat.mod_mod _ _).symm
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      fun h => vecn_transfer n N _ (hodd N hN) (hmododd N hN) hm h⟩
    · rwa [vecn_transfer n N _ (hodd N hN) (hmododd N hN) hm h]
    · rwa [vecn_transfer n (N % 2 ^ (3 * n)) N (hmododd N hN) (hodd N hN) hm.symm h]
  have h1 : pm S w (fun N => E (vecn n N) ∧ vecn n N ∈ Tset n) =
      pm S w (fun N => E (vecn n (N % 2 ^ (3 * n))) ∧ vecn n (N % 2 ^ (3 * n)) ∈ Tset n) := by
    apply pm_congr
    intro N hN
    constructor
    · rintro ⟨hE, hT⟩
      exact ⟨by rw [(hTiff N hN).2 hT]; exact hE, (hTiff N hN).1.1 hT⟩
    · rintro ⟨hE, hT⟩
      have hT' := (hTiff N hN).1.2 hT
      exact ⟨by rw [← (hTiff N hN).2 hT']; exact hE, hT'⟩
  have h2 : pm S w (fun N => vecn n N ∉ Tset n) =
      pm S w (fun N => vecn n (N % 2 ^ (3 * n)) ∉ Tset n) := by
    apply pm_congr
    intro N hN
    exact not_congr (hTiff N hN).1
  have hU' : ∀ (P : ℕ → Prop) [DecidablePred P], |pm S w (fun N => P (N % 2 ^ (3 * n))) -
      (((Rset n).filter P).card : ℝ) / 2 ^ (3 * n - 1)| ≤ K * (1 / 2) ^ (3 * n) := by
    intro P _
    convert hU P
  have hU1 := hU' (fun r => E (vecn n r) ∧ vecn n r ∈ Tset n)
  have hU2 := hU' (fun r => vecn n r ∉ Tset n)
  beta_reduce at hU1 hU2
  rw [← h1, U_vec_E] at hU1
  rw [← h2] at hU2
  have htail := U_tail n hn
  have hsplit := pm_split S w (fun N => E (vecn n N)) (fun N => vecn n N ∈ Tset n)
  have hle : pm S w (fun N => E (vecn n N) ∧ ¬ vecn n N ∈ Tset n) ≤
      pm S w (fun N => vecn n N ∉ Tset n) := pm_mono S w hw (fun N _ h => h.2)
  have h0 := pm_nonneg S w hw (fun N => E (vecn n N) ∧ ¬ vecn n N ∈ Tset n)
  obtain ⟨hs1, hs2⟩ := small_terms n
  have hU2' := (abs_le.1 hU2).2
  have hU1' := abs_le.1 hU1
  rw [abs_le]
  constructor <;> nlinarith

/-! Hypothesis (1.11) for `N_y` (Tao (5.4), "routine integral test"): residue classes of a
decreasing weight on an interval have nearly equal mass. -/

lemma class_sum_blocks (f : ℕ → ℝ) (a b M r : ℕ) (hM : 0 < M) (hr : r < M) :
    ∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r), f N =
      ∑ j ∈ Finset.range (b / M + 1),
        if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0 := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun j => j * M + r) (fun N => N / M)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
    refine ⟨hj.2, ?_⟩
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hN ⊢
    have hd := Nat.div_add_mod N M
    rw [hN.2] at hd
    have hN' : N / M * M + r = N := by rw [mul_comm]; exact hd
    rw [hN']
    exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hN.1.2), hN.1⟩
  · intro j _
    rw [add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hr, zero_add]
  · intro N hN
    simp only [Finset.mem_filter] at hN
    have hd := Nat.div_add_mod N M
    rw [hN.2] at hd
    rw [mul_comm]; exact hd
  · intro j _
    rfl

lemma class_sum_close (f : ℕ → ℝ) (hf : ∀ m n, 1 ≤ m → m ≤ n → f n ≤ f m) (hf0 : ∀ n, 0 ≤ f n)
    (a b M r r' : ℕ) (hM : 0 < M) (hr : r < M) (hr' : r' < M) (haM : M ≤ a) :
    |∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r), f N -
      ∑ N ∈ (Finset.Icc a b).filter (fun N => N % M = r'), f N| ≤ f (a / M * M) + 2 * f a := by
  rw [class_sum_blocks f a b M r hM hr, class_sum_blocks f a b M r' hM hr',
    ← Finset.sum_sub_distrib]
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = a / M := ⟨_, rfl⟩
  rw [← hj0]
  have hj01 : 1 ≤ j0 := by
    rw [hj0]; exact (Nat.one_le_div_iff hM).2 haM
  let g : ℕ → ℝ := fun j => if j0 ≤ j then f (j * M) - f ((j + 1) * M) else 0
  have hjM : ∀ j, j0 ≤ j → 1 ≤ j * M := fun j hj =>
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    simp only [g]
    split_ifs with h
    · linarith [hf (j * M) ((j + 1) * M) (hjM j h) (by nlinarith)]
    · exact le_refl _
  have hone : ∀ j s s', s < M → s' < M → (a ≤ j * M + s ∧ j * M + s ≤ b) →
      ¬ (a ≤ j * M + s' ∧ j * M + s' ≤ b) → j = j0 ∨ j = b / M := by
    intro j s s' hs hs' h hn
    have hsucc : (j + 1) * M = j * M + M := by ring
    by_cases h3 : a ≤ j * M + s'
    · right
      have h4 : b < j * M + s' := by
        by_contra h5; exact hn ⟨h3, by omega⟩
      exact (Nat.div_eq_of_lt_le (by omega) (by rw [hsucc]; omega)).symm
    · left
      rw [hj0]
      exact (Nat.div_eq_of_lt_le (by omega) (by rw [hsucc]; omega)).symm
  have hpt : ∀ j, |(if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0) -
      (if a ≤ j * M + r' ∧ j * M + r' ≤ b then f (j * M + r') else 0)| ≤
      g j + ((if j = j0 then f a else 0) + (if j = b / M then f a else 0)) := by
    intro j
    have hfa : ∀ s, a ≤ j * M + s → f (j * M + s) ≤ f a := fun s hs => hf a _ (by omega) hs
    have hite0 : 0 ≤ (if j = j0 then f a else 0) := by split_ifs <;> simp [hf0]
    have hite1 : 0 ≤ (if j = b / M then f a else 0) := by split_ifs <;> simp [hf0]
    have hboth : ∀ s, s < M → a ≤ j * M + s → j0 ≤ j := by
      intro s hs h
      rw [hj0]
      have : a < (j + 1) * M := by nlinarith
      exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hM).2 this)
    have hrhs : ∀ s, s < M → a ≤ j * M + s → f (j * M + s) ≤
        (if j = j0 then f a else 0) + (if j = b / M then f a else 0) → True := fun _ _ _ _ => trivial
    by_cases hp : a ≤ j * M + r ∧ j * M + r ≤ b <;> by_cases hp' : a ≤ j * M + r' ∧ j * M + r' ≤ b
    · rw [if_pos hp, if_pos hp']
      have hj := hboth r hr hp.1
      have hgj : g j = f (j * M) - f ((j + 1) * M) := by simp only [g]; rw [if_pos hj]
      have h1 := hjM j hj
      have e1 := hf (j * M) (j * M + r) h1 (by omega)
      have e2 := hf (j * M) (j * M + r') h1 (by omega)
      have e3 := hf (j * M + r) ((j + 1) * M) (by omega) (by nlinarith)
      have e4 := hf (j * M + r') ((j + 1) * M) (by omega) (by nlinarith)
      rw [abs_sub_le_iff]
      constructor <;> linarith
    · rw [if_pos hp, if_neg hp', sub_zero, abs_of_nonneg (hf0 _)]
      have := hfa r hp.1
      rcases hone j r r' hr hr' hp hp' with h | h
      · rw [if_pos h]; linarith [hg0 j]
      · rw [if_pos h]; linarith [hg0 j]
    · rw [if_neg hp, if_pos hp', zero_sub, abs_neg, abs_of_nonneg (hf0 _)]
      have := hfa r' hp'.1
      rcases hone j r' r hr' hr hp' hp with h | h
      · rw [if_pos h]; linarith [hg0 j]
      · rw [if_pos h]; linarith [hg0 j]
    · rw [if_neg hp, if_neg hp', sub_zero, abs_zero]
      linarith [hg0 j]
  have htel : ∀ n, ∑ j ∈ Finset.range n, g j ≤ f (j0 * M) := by
    have key : ∀ n, ∑ j ∈ Finset.range n, g j =
        if n ≤ j0 then 0 else f (j0 * M) - f (n * M) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [g]
        split_ifs <;> first
          | ring1
          | (exfalso; omega)
          | (rw [show n = j0 by omega]; ring1)
    intro n
    rw [key]
    split_ifs
    · exact hf0 _
    · linarith [hf0 (n * M)]
  have hsum1 : ∑ j ∈ Finset.range (b / M + 1), (if j = j0 then f a else 0) ≤ f a := by
    rw [Finset.sum_ite_eq']; split_ifs <;> simp [hf0]
  have hsum2 : ∑ j ∈ Finset.range (b / M + 1), (if j = b / M then f a else 0) ≤ f a := by
    rw [Finset.sum_ite_eq']; split_ifs <;> simp [hf0]
  calc _ ≤ ∑ j ∈ Finset.range (b / M + 1), |(if a ≤ j * M + r ∧ j * M + r ≤ b then f (j * M + r) else 0) -
        (if a ≤ j * M + r' ∧ j * M + r' ≤ b then f (j * M + r') else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (b / M + 1),
        (g j + ((if j = j0 then f a else 0) + (if j = b / M then f a else 0))) :=
        Finset.sum_le_sum (fun j _ => hpt j)
    _ = ∑ j ∈ Finset.range (b / M + 1), g j +
        (∑ j ∈ Finset.range (b / M + 1), (if j = j0 then f a else 0) +
          ∑ j ∈ Finset.range (b / M + 1), (if j = b / M then f a else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ f (j0 * M) + 2 * f a := by linarith [htel (b / M + 1)]

/-- Tao's `α = 1.001` (1.18). -/
noncomputable def alph : ℝ := 1001 / 1000

open Classical in
/-- Odd integers in `[y, y^α]`, the support of `N_y`. -/
noncomputable def oddIcc (y : ℝ) : Finset ℕ := (Finset.Icc ⌈y⌉₊ ⌊y ^ alph⌋₊).filter Odd

/-- Normaliser of the log-uniform weight `1/N` on `oddIcc y`. -/
noncomputable def Z (y : ℝ) : ℝ := ∑ N ∈ oddIcc y, (1 : ℝ) / N

open Classical in
/-- `P(Q(N_y))` for the log-uniform odd variable `N_y` on `[y, y^α]`. -/
noncomputable def prob (y : ℝ) (Q : ℕ → Prop) : ℝ :=
  (∑ N ∈ oddIcc y, if Q N then (1 : ℝ) / N else 0) / Z y

/-- `T_x(N) < ∞`: the orbit of `N` reaches `x` or below. -/
def Reaches (x : ℝ) (N : ℕ) : Prop := ∃ n, (syracuseStep^[n] N : ℝ) ≤ x

open Classical in
/-- First passage time `T_x(N)` (junk value 0 when the orbit never reaches `x`). -/
noncomputable def T (x : ℝ) (N : ℕ) : ℕ := if h : Reaches x N then Nat.find h else 0

/-- First passage location `Pass_x(N) = Syr^{T_x(N)}(N)`. -/
noncomputable def Pass (x : ℝ) (N : ℕ) : ℕ := syracuseStep^[T x N] N

lemma pass_le (x : ℝ) (N : ℕ) (h : Reaches x N) : (Pass x N : ℝ) ≤ x := by
  unfold Pass T; rw [dif_pos h]; exact Nat.find_spec h

lemma T_le (x : ℝ) (N n : ℕ) (h : (syracuseStep^[n] N : ℝ) ≤ x) : T x N ≤ n := by
  have hr : Reaches x N := ⟨n, h⟩
  unfold T; rw [dif_pos hr]; exact Nat.find_min' hr h

lemma reaches_mono {x x' : ℝ} (hxx : x ≤ x') {N : ℕ} (h : Reaches x N) : Reaches x' N := by
  obtain ⟨n, hn⟩ := h; exact ⟨n, hn.trans hxx⟩

lemma reaches_of_le {x : ℝ} {N : ℕ} (h : (N : ℝ) ≤ x) : Reaches x N := ⟨0, by simpa using h⟩

lemma orbitMin_le_orbitMin_pass (x : ℝ) (N : ℕ) :
    syracuseOrbitMin N ≤ syracuseOrbitMin (Pass x N) :=
  orbitMin_le_orbitMin_iterate N _

lemma orbitMin_pass_le (x : ℝ) (N : ℕ) (h : Reaches x N) : (syracuseOrbitMin (Pass x N) : ℝ) ≤ x :=
  le_trans (by exact_mod_cast orbitMin_le_self _) (pass_le x N h)

/-- Tao Sec 3 observation: the first passage below a higher level `x'` comes no later, so its
orbit minimum is at most that of the first passage below `x`. -/
lemma orbitMin_pass_mono {x x' : ℝ} (hxx : x ≤ x') {N : ℕ} (h : Reaches x N) :
    syracuseOrbitMin (Pass x' N) ≤ syracuseOrbitMin (Pass x N) := by
  have hle : T x' N ≤ T x N := T_le x' N (T x N) ((pass_le x N h).trans hxx)
  have hit : Pass x N = syracuseStep^[T x N - T x' N] (Pass x' N) := by
    unfold Pass; rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
  rw [hit]
  exact orbitMin_le_orbitMin_iterate _ _

lemma Z_nonneg (y : ℝ) : 0 ≤ Z y := Finset.sum_nonneg (fun N _ => by positivity)

lemma prob_nonneg (y : ℝ) (Q : ℕ → Prop) : 0 ≤ prob y Q := by
  unfold prob
  apply div_nonneg _ (Z_nonneg y)
  apply Finset.sum_nonneg; intro N _; split_ifs <;> positivity

lemma prob_add_compl (y : ℝ) (hZ : 0 < Z y) (Q : ℕ → Prop) :
    prob y Q + prob y (fun N => ¬ Q N) = 1 := by
  unfold prob
  rw [← add_div, ← Finset.sum_add_distrib, div_eq_one_iff_eq hZ.ne']
  unfold Z; apply Finset.sum_congr rfl; intro N _; by_cases h : Q N <;> simp [h]

lemma prob_mono (y : ℝ) {P Q : ℕ → Prop} (hPQ : ∀ N, P N → Q N) : prob y P ≤ prob y Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ (Z_nonneg y)
  apply Finset.sum_le_sum; intro N _
  by_cases hP : P N
  · simp [hP, hPQ N hP]
  · by_cases hQ : Q N <;> simp [hP, hQ] <;> positivity

lemma prob_le_and_add (y : ℝ) (P Q : ℕ → Prop) :
    prob y P ≤ prob y (fun N => P N ∧ Q N) + prob y (fun N => ¬ Q N) := by
  unfold prob
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Z_nonneg y)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro N _
  by_cases hP : P N <;> by_cases hQ : Q N <;> simp [hP, hQ] <;> positivity

/-- Lean interface for Tao Prop 1.11 [(1.19) and (1.20), the latter in event form, which is
equivalent to the total-variation bound]. Section 3 derives the leaf from this. -/
def Prop111 : Prop :=
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    prob (x ^ alph) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
    prob (x ^ (alph ^ 2)) (fun N => ¬ Reaches x N) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
        prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤ C * Real.log x ^ (-c)

/-! DECOMPOSE item 5, Section 3 telescoping. -/

/-- Tao's event `B_x` (for `N0`): the orbit reaches `x`, then has orbit minimum `≤ N0`. -/
def Bev (x N0 : ℝ) (N : ℕ) : Prop := Reaches x N ∧ (syracuseOrbitMin (Pass x N) : ℝ) ≤ N0

lemma Bev_mono {x x' N0 : ℝ} (hxx : x ≤ x') {N : ℕ} (h : Bev x N0 N) : Bev x' N0 N :=
  ⟨reaches_mono hxx h.1, le_trans (by exact_mod_cast orbitMin_pass_mono hxx h.1) h.2⟩

lemma alph_pos : 0 < alph := by unfold alph; norm_num

lemma one_lt_alph : 1 < alph := by unfold alph; norm_num

lemma rpow_alph_sq (x : ℝ) (hx : 0 ≤ x) : x ^ (alph ^ 2) = (x ^ alph) ^ alph := by
  rw [pow_two, Real.rpow_mul hx]

lemma le_rpow_alph {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ alph := by
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ alph := Real.rpow_le_rpow_of_exponent_le hx one_lt_alph.le

/-- One telescoping step (Tao Sec 3): `P(B_{x^α}) ≥ P(B_x) - ε` from (1.20) at level `x`. -/
lemma step_B (x N0 ε : ℝ) (hx : 1 ≤ x)
    (hE : ∀ E : ℕ → Prop,
      |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
        prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤ ε) :
    prob (x ^ alph) (Bev x N0) - ε ≤ prob ((x ^ alph) ^ alph) (Bev (x ^ alph) N0) := by
  have h := hE (fun P => (syracuseOrbitMin P : ℝ) ≤ N0)
  have h1 := (abs_sub_le_iff.mp h).1
  have h2 : prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ (syracuseOrbitMin (Pass x N) : ℝ) ≤ N0)
      ≤ prob ((x ^ alph) ^ alph) (Bev (x ^ alph) N0) := by
    rw [rpow_alph_sq x (by linarith)]
    exact prob_mono _ (fun N hN => Bev_mono (le_rpow_alph hx) hN)
  have h3 : prob (x ^ alph) (Bev x N0)
      = prob (x ^ alph) (fun N => Reaches x N ∧ (syracuseOrbitMin (Pass x N) : ℝ) ≤ N0) := rfl
  linarith

lemma telescope (q e : ℕ → ℝ) (h : ∀ j, q j - e j ≤ q (j + 1)) (J : ℕ) :
    q 0 - ∑ j ∈ Finset.range J, e j ≤ q J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ]; linarith [h J]

lemma rpow_alph_pow_succ (y : ℝ) (hy : 0 ≤ y) (j : ℕ) :
    y ^ (alph ^ (j + 1)) = (y ^ (alph ^ j)) ^ alph := by
  rw [pow_succ, Real.rpow_mul hy]

/-- Geometric control of the telescoping errors `C (log y^{α^j})^{-c}`. -/
lemma err_sum_le (C c L : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hL : 0 < L) (J : ℕ) :
    ∑ j ∈ Finset.range J, C * (alph ^ j * L) ^ (-c) ≤ C * L ^ (-c) * (1 / (1 - alph ^ (-c))) := by
  have hr0 : 0 ≤ alph ^ (-c) := Real.rpow_nonneg alph_pos.le _
  have hr1 : alph ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_alph (by linarith)
  have hterm : ∀ j : ℕ, C * (alph ^ j * L) ^ (-c) = C * L ^ (-c) * (alph ^ (-c)) ^ j := by
    intro j
    rw [Real.mul_rpow (pow_pos alph_pos j).le hL.le, ← Real.rpow_natCast alph j,
      ← Real.rpow_mul alph_pos.le, mul_comm (j : ℝ), Real.rpow_mul alph_pos.le, Real.rpow_natCast]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hL.le _))
  have hg := geom_sum_mul_neg (alph ^ (-c)) J
  rw [le_div_iff₀ (by linarith), hg]
  linarith [pow_nonneg hr0 J]

lemma le_rpow_alph_pow {y : ℝ} (hy : 1 ≤ y) (j : ℕ) : y ≤ y ^ (alph ^ j) := by
  calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
    _ ≤ y ^ (alph ^ j) := Real.rpow_le_rpow_of_exponent_le hy (one_le_pow₀ one_lt_alph.le)

/-- Telescoped chain (Tao Sec 3): `P(B_{y^{α^J}}) ≥ P(B_y) - O(log^{-c} y)` uniformly in `J`. -/
lemma chain_B (y x0 N0 C c : ℝ) (hy : 1 < y) (hy0 : x0 ≤ y) (hC : 0 ≤ C) (hc : 0 < c)
    (hE : ∀ x : ℝ, x0 ≤ x → ∀ E : ℕ → Prop,
      |prob (x ^ alph) (fun N => Reaches x N ∧ E (Pass x N)) -
        prob (x ^ (alph ^ 2)) (fun N => Reaches x N ∧ E (Pass x N))| ≤ C * Real.log x ^ (-c))
    (J : ℕ) :
    prob (y ^ alph) (Bev y N0) - C * Real.log y ^ (-c) * (1 / (1 - alph ^ (-c)))
      ≤ prob ((y ^ (alph ^ J)) ^ alph) (Bev (y ^ (alph ^ J)) N0) := by
  have hy0' : 0 < y := by linarith
  have hL : 0 < Real.log y := Real.log_pos hy
  set q : ℕ → ℝ := fun j => prob ((y ^ (alph ^ j)) ^ alph) (Bev (y ^ (alph ^ j)) N0) with hq
  set e : ℕ → ℝ := fun j => C * (alph ^ j * Real.log y) ^ (-c) with he
  have hstep : ∀ j, q j - e j ≤ q (j + 1) := by
    intro j
    have hxj : 1 ≤ y ^ (alph ^ j) := le_trans hy.le (le_rpow_alph_pow hy.le j)
    have h := step_B (y ^ (alph ^ j)) N0 _ hxj (hE _ (le_trans hy0 (le_rpow_alph_pow hy.le j)))
    rw [Real.log_rpow hy0'] at h
    simp only [hq, he]
    rw [rpow_alph_pow_succ y hy0'.le j]
    exact h
  have ht := telescope q e hstep J
  have hs : ∑ j ∈ Finset.range J, e j ≤ C * Real.log y ^ (-c) * (1 / (1 - alph ^ (-c))) :=
    err_sum_le C c (Real.log y) hC hc hL J
  have h0 : q 0 = prob (y ^ alph) (Bev y N0) := by simp [hq]
  have hJ : q J = prob ((y ^ (alph ^ J)) ^ alph) (Bev (y ^ (alph ^ J)) N0) := rfl
  rw [h0, hJ] at ht
  linarith

/-- Base of the chain: below `N0`, reaching `y` already forces `B_y`. -/
lemma base_B (y N0 : ℝ) (h : y ≤ N0) :
    prob (y ^ alph) (fun N => Reaches y N) ≤ prob (y ^ alph) (Bev y N0) :=
  prob_mono _ (fun N hN => ⟨hN, (orbitMin_pass_le y N hN).trans h⟩)

/-- End of the chain: `B_z` for `N_{z^α}` forces `Syr_min(N) ≤ N0`. -/
lemma bad_le (z N0 : ℝ) (hZ : 0 < Z (z ^ alph)) :
    prob (z ^ alph) (fun N => N0 < (syracuseOrbitMin N : ℝ)) ≤ 1 - prob (z ^ alph) (Bev z N0) := by
  have h1 := prob_add_compl _ hZ (Bev z N0)
  have h2 : prob (z ^ alph) (fun N => N0 < (syracuseOrbitMin N : ℝ))
      ≤ prob (z ^ alph) (fun N => ¬ Bev z N0 N) := by
    apply prob_mono
    intro N hN hB
    have h3 : (syracuseOrbitMin N : ℝ) ≤ syracuseOrbitMin (Pass z N) := by
      exact_mod_cast orbitMin_le_orbitMin_pass z N
    linarith [hB.2]
  linarith

lemma prob_reaches (y x : ℝ) (hZ : 0 < Z y) :
    prob y (fun N => Reaches x N) = 1 - prob y (fun N => ¬ Reaches x N) := by
  have := prob_add_compl y hZ (fun N => Reaches x N)
  linarith

/-! DECOMPOSE item 5c support: the support of `N_y` is nonempty for `y ≥ 1000`. -/

lemma add_three_le_rpow_alph {y : ℝ} (hy : 1000 ≤ y) : y + 3 ≤ y ^ alph := by
  have hy0 : 0 < y := by linarith
  have hsplit : y ^ alph = y * y ^ (alph - 1) := by
    rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
  have hlog : (6 : ℝ) ≤ Real.log y := by
    have h1 : Real.log 1000 ≤ Real.log y := Real.log_le_log (by norm_num) hy
    have h2 : (6 : ℝ) < Real.log 1000 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      calc Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 2.7182818286 ^ 6 := by gcongr
        _ < 1000 := by norm_num
    linarith
  have ha : alph - 1 = 1 / 1000 := by unfold alph; norm_num
  have hexp : 1 + 1 / 1000 * Real.log y ≤ y ^ (alph - 1) := by
    rw [Real.rpow_def_of_pos hy0, ha]
    have := Real.add_one_le_exp (Real.log y * (1 / 1000))
    linarith
  have h1 : y * (1 + 1 / 1000 * Real.log y) ≤ y * y ^ (alph - 1) :=
    mul_le_mul_of_nonneg_left hexp hy0.le
  have h2 : 1000 * 6 ≤ y * Real.log y := mul_le_mul hy hlog (by norm_num) hy0.le
  rw [hsplit]
  nlinarith [h1, h2]

lemma Z_pos {y : ℝ} (hy : 1000 ≤ y) : 0 < Z y := by
  have h3 := add_three_le_rpow_alph hy
  have hm1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨N, hN, hNodd⟩ : ∃ N, (N = ⌈y⌉₊ ∨ N = ⌈y⌉₊ + 1) ∧ Odd N := by
    rcases Nat.even_or_odd ⌈y⌉₊ with h | h
    · exact ⟨⌈y⌉₊ + 1, Or.inr rfl, h.add_one⟩
    · exact ⟨⌈y⌉₊, Or.inl rfl, h⟩
  have hNle : (N : ℝ) ≤ ⌈y⌉₊ + 1 := by
    rcases hN with rfl | rfl <;> push_cast <;> linarith
  have hNmem : N ∈ oddIcc y := by
    unfold oddIcc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, Nat.le_floor (by linarith)⟩, hNodd⟩
  have hN0 : 0 < N := by obtain ⟨k, hk⟩ := hNodd; omega
  unfold Z
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨N, hNmem, one_div_pos.mpr (Nat.cast_pos.mpr hN0)⟩

/-! DECOMPOSE item 5c: per-interval bound. -/

lemma prob_bad_zero (z N0 : ℝ) (hz : 0 ≤ z) (h : z ^ (alph ^ 2) ≤ N0) :
    prob (z ^ alph) (fun N => N0 < (syracuseOrbitMin N : ℝ)) = 0 := by
  unfold prob
  rw [Finset.sum_eq_zero, zero_div]
  intro N hN
  rw [if_neg]
  intro hlt
  unfold oddIcc at hN
  rw [Finset.mem_filter, Finset.mem_Icc] at hN
  have h1 : (N : ℝ) ≤ (z ^ alph) ^ alph := by
    have hp : 0 ≤ (z ^ alph) ^ alph := by positivity
    exact (Nat.cast_le.mpr hN.1.2).trans (Nat.floor_le hp)
  rw [← rpow_alph_sq z hz] at h1
  have h2 : (syracuseOrbitMin N : ℝ) ≤ N := by exact_mod_cast orbitMin_le_self N
  linarith

lemma exists_scale (z N0 : ℝ) (hz : 1 < z) (hN0 : 1 < N0) (h : N0 < z ^ (alph ^ 2)) :
    ∃ y : ℝ, ∃ J : ℕ, 1 < y ∧ y ≤ N0 ∧ Real.log N0 ≤ alph ^ 2 * Real.log y ∧
      y ^ (alph ^ J) = z := by
  classical
  have hL : 0 < Real.log z := Real.log_pos hz
  have hL0 : 0 < Real.log N0 := Real.log_pos hN0
  have hex : ∃ J : ℕ, Real.log z ≤ alph ^ J * Real.log N0 := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (Real.log z / Real.log N0) one_lt_alph
    exact ⟨J, by rw [div_lt_iff₀ hL0] at hJ; linarith⟩
  obtain ⟨J, hJ, hJmin⟩ : ∃ J : ℕ, Real.log z ≤ alph ^ J * Real.log N0 ∧
      ∀ j < J, ¬ Real.log z ≤ alph ^ j * Real.log N0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hapos : ∀ j : ℕ, 0 < alph ^ j := fun j => pow_pos alph_pos j
  have ha1 := one_lt_alph
  refine ⟨Real.exp (Real.log z / alph ^ J), J, ?_, ?_, ?_, ?_⟩
  · have hq : 0 < Real.log z / alph ^ J := div_pos hL (hapos _)
    have := Real.add_one_lt_exp hq.ne'
    linarith
  · rw [← Real.exp_log (by linarith : 0 < N0)]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (hapos _)]; linarith
  · rw [Real.log_exp]
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0, pow_zero, div_one]
      have h3 := Real.log_lt_log (by linarith) h
      rw [Real.log_rpow (by linarith)] at h3
      linarith
    · have hlt : ¬ Real.log z ≤ alph ^ (J - 1) * Real.log N0 :=
        hJmin _ (by omega)
      push_neg at hlt
      have hJeq : alph ^ J = alph ^ (J - 1) * alph := by
        rw [← pow_succ]; congr 1; omega
      have ha := hapos (J - 1)
      have hq : Real.log N0 < Real.log z / alph ^ (J - 1) := by
        rw [lt_div_iff₀ ha]; linarith
      have hne : alph ≠ 0 := alph_pos.ne'
      have he : alph ^ 2 * (Real.log z / alph ^ J) =
          alph * (Real.log z / alph ^ (J - 1)) := by
        rw [hJeq]; field_simp; try ring
      rw [he]
      nlinarith
  · rw [← Real.exp_mul, div_mul_cancel₀ _ (hapos _).ne', Real.exp_log (by linarith)]

/-- Per-interval bound (Tao Sec 3): `P(Syr_min(N_{z^α}) > N0) ≪ log^{-c} N0`, uniformly in `z`. -/
lemma interval_bound (hP : Prop111) : ∃ C' c M0 : ℝ, 0 < C' ∧ 0 < c ∧ 1 < M0 ∧
    ∀ N0 z : ℝ, M0 ≤ N0 → 1 ≤ z →
      prob (z ^ alph) (fun N => N0 < (syracuseOrbitMin N : ℝ)) ≤ C' * Real.log N0 ^ (-c) := by
  obtain ⟨C, c, x0, hC, hc, hP⟩ := hP
  set B := max x0 1000 with hB
  set K : ℝ := 1 / (1 - alph ^ (-c)) with hK
  have hK0 : 0 < K := by
    have : alph ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_alph (by linarith)
    rw [hK]; apply one_div_pos.mpr; linarith
  have ha2 : (0 : ℝ) < alph ^ 2 := by have := alph_pos; positivity
  have hCK : 0 < C * (1 + K) := mul_pos hC (by linarith)
  have hC' : 0 < C * (1 + K) * (alph ^ 2) ^ c := mul_pos hCK (Real.rpow_pos_of_pos ha2 _)
  have hB1 : (1000 : ℝ) ≤ B := le_max_right _ _
  have hBpos : 0 < B := by linarith
  refine ⟨C * (1 + K) * (alph ^ 2) ^ c, c, B ^ (alph ^ 2), hC', hc,
    Real.one_lt_rpow (by linarith) ha2, ?_⟩
  intro N0 z hN0 hz
  have hN0' : 1 < N0 := lt_of_lt_of_le (Real.one_lt_rpow (by linarith) ha2) hN0
  have hN0l : 0 < Real.log N0 := Real.log_pos hN0'
  have hz0 : (0 : ℝ) ≤ z := by linarith
  by_cases hsmall : z ^ (alph ^ 2) ≤ N0
  · rw [prob_bad_zero z N0 hz0 hsmall]
    exact mul_nonneg hC'.le (Real.rpow_nonneg hN0l.le _)
  push_neg at hsmall
  have hz1 : 1 < z := by
    by_contra hcon
    push_neg at hcon
    have : z ^ (alph ^ 2) ≤ 1 := Real.rpow_le_one hz0 hcon ha2.le
    linarith
  obtain ⟨y, J, hy1, hyN0, hlog, hyz⟩ := exists_scale z N0 hz1 hN0' hsmall
  have hlogB : alph ^ 2 * Real.log B ≤ Real.log N0 := by
    have := Real.log_le_log (by positivity) hN0
    rwa [Real.log_rpow hBpos] at this
  have hyB : B ≤ y := by
    have h1 : Real.log B ≤ Real.log y := by nlinarith
    exact (Real.log_le_log_iff hBpos (by linarith)).mp h1
  have hy0 : x0 ≤ y := le_trans (le_max_left _ _) hyB
  have hy1000 : 1000 ≤ y := le_trans hB1 hyB
  have hzy : y ≤ z := by rw [← hyz]; exact le_rpow_alph_pow hy1.le J
  have hZz : 0 < Z (z ^ alph) :=
    Z_pos (le_trans hy1000 (le_trans hzy (le_rpow_alph (by linarith))))
  have hZy : 0 < Z (y ^ alph) := Z_pos (le_trans hy1000 (le_rpow_alph (by linarith)))
  have hch := chain_B y x0 N0 C c hy1 hy0 hC.le hc (fun x hx E => (hP x hx).2.2 E) J
  rw [hyz, ← hK] at hch
  have hbad := bad_le z N0 hZz
  have hbase := base_B y N0 hyN0
  have hreach := prob_reaches (y ^ alph) y hZy
  have hnr := (hP y hy0).1
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hyc : y ^ (-c) ≤ Real.log y ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hly (Real.log_le_self (by linarith)) (by linarith)
  have hlogc : Real.log y ^ (-c) ≤ (alph ^ 2) ^ c * Real.log N0 ^ (-c) := by
    have h1 : Real.log N0 / alph ^ 2 ≤ Real.log y := by
      rw [div_le_iff₀ ha2]; linarith
    have h2 := Real.rpow_le_rpow_of_nonpos (div_pos hN0l ha2) h1 (by linarith : -c ≤ 0)
    rw [Real.div_rpow hN0l.le ha2.le, Real.rpow_neg ha2.le, div_inv_eq_mul] at h2
    calc Real.log y ^ (-c) ≤ Real.log N0 ^ (-c) * (alph ^ 2) ^ c := h2
      _ = (alph ^ 2) ^ c * Real.log N0 ^ (-c) := by ring
  have e1 : C * y ^ (-c) ≤ C * Real.log y ^ (-c) := mul_le_mul_of_nonneg_left hyc hC.le
  have e2 : C * (1 + K) * Real.log y ^ (-c) ≤
      C * (1 + K) * ((alph ^ 2) ^ c * Real.log N0 ^ (-c)) :=
    mul_le_mul_of_nonneg_left hlogc hCK.le
  have e3 : C * Real.log y ^ (-c) * K + C * Real.log y ^ (-c) =
      C * (1 + K) * Real.log y ^ (-c) := by ring
  have e4 : C * (1 + K) * ((alph ^ 2) ^ c * Real.log N0 ^ (-c)) =
      C * (1 + K) * (alph ^ 2) ^ c * Real.log N0 ^ (-c) := by ring
  linarith

/-! DECOMPOSE item 5d: covering `(M, x]` by the intervals `[W_{j+1}, W_j]`, `W_j = x^{α^{-j}}`. -/

open Classical in
lemma num_le (y : ℝ) (Q : ℕ → Prop) :
    (∑ N ∈ oddIcc y, if Q N then (1 : ℝ) / N else 0) ≤ Z y * prob y Q := by
  rcases eq_or_ne (Z y) 0 with h | h
  · rw [h, zero_mul]
    have h' : (∑ N ∈ oddIcc y, (1 : ℝ) / N) = 0 := h
    calc (∑ N ∈ oddIcc y, if Q N then (1 : ℝ) / N else 0) ≤ ∑ N ∈ oddIcc y, (1 : ℝ) / N :=
          Finset.sum_le_sum (fun N _ => by split_ifs <;> first | exact le_rfl | positivity)
      _ = 0 := h'
  · unfold prob
    apply le_of_eq
    field_simp

lemma inv_le_log_sub {n : ℝ} (hn : 1 < n) : 1 / n ≤ Real.log n - Real.log (n - 1) := by
  have h1 : 0 < n - 1 := by linarith
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; linarith
  have h := Real.log_le_sub_one_of_pos (div_pos h1 (by linarith : (0 : ℝ) < n))
  rw [Real.log_div h1.ne' hn0, sub_div, div_self hn0] at h
  linarith

lemma harm_range (a : ℕ) (ha : 1 ≤ a) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (1 : ℝ) / ((a : ℝ) + i) ≤
      1 / a + Real.log ((a : ℝ) + m) - Real.log a := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have h := inv_le_log_sub (show (1 : ℝ) < (a : ℝ) + ((m + 1 : ℕ) : ℝ) by push_cast; linarith)
    have e : (a : ℝ) + ((m + 1 : ℕ) : ℝ) - 1 = (a : ℝ) + m := by push_cast; ring
    rw [e] at h
    linarith

/-- Harmonic bound for the normaliser: `Z(w) ≤ 1 + (α - 1) log w`. -/
lemma Z_le {w : ℝ} (hw : 1 ≤ w) : Z w ≤ 1 + (alph - 1) * Real.log w := by
  have hlw : 0 ≤ Real.log w := Real.log_nonneg hw
  have ha1 := one_lt_alph
  have ha : 1 ≤ ⌈w⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have haw : w ≤ (⌈w⌉₊ : ℝ) := Nat.le_ceil w
  rcases lt_or_ge ⌊w ^ alph⌋₊ ⌈w⌉₊ with hlt | hle
  · have : oddIcc w = ∅ := by
      unfold oddIcc; rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty]
    unfold Z; rw [this, Finset.sum_empty]; nlinarith
  · have hsub : Z w ≤ ∑ n ∈ Finset.Icc ⌈w⌉₊ ⌊w ^ alph⌋₊, (1 : ℝ) / n := by
      unfold Z oddIcc
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => by positivity)
    have hIcc : ∑ n ∈ Finset.Icc ⌈w⌉₊ ⌊w ^ alph⌋₊, (1 : ℝ) / n =
        ∑ i ∈ Finset.range (⌊w ^ alph⌋₊ - ⌈w⌉₊ + 1), (1 : ℝ) / ((⌈w⌉₊ : ℝ) + i) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
        show ⌊w ^ alph⌋₊ + 1 - ⌈w⌉₊ = ⌊w ^ alph⌋₊ - ⌈w⌉₊ + 1 by omega]
      exact Finset.sum_congr rfl (fun i _ => by norm_num)
    have hh := harm_range ⌈w⌉₊ ha (⌊w ^ alph⌋₊ - ⌈w⌉₊)
    have hcast : ((⌈w⌉₊ : ℝ) + ((⌊w ^ alph⌋₊ - ⌈w⌉₊ : ℕ) : ℝ)) = (⌊w ^ alph⌋₊ : ℝ) := by
      rw [Nat.cast_sub hle]; ring
    rw [hcast] at hh
    have hb : (⌊w ^ alph⌋₊ : ℝ) ≤ w ^ alph := Nat.floor_le (by positivity)
    have ha'' : (1 : ℝ) ≤ ⌈w⌉₊ := by exact_mod_cast ha
    have hab : (⌈w⌉₊ : ℝ) ≤ ⌊w ^ alph⌋₊ := by exact_mod_cast hle
    have hlogb : Real.log ⌊w ^ alph⌋₊ ≤ alph * Real.log w := by
      rw [← Real.log_rpow (by linarith)]; exact Real.log_le_log (by linarith) hb
    have hloga : Real.log w ≤ Real.log ⌈w⌉₊ := Real.log_le_log (by linarith) haw
    have hinv : 1 / (⌈w⌉₊ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact ha''
    linarith

lemma geom_alph (J : ℕ) :
    ∑ j ∈ Finset.range J, (alph - 1) / alph ^ (j + 1) = 1 - 1 / alph ^ J := by
  have hne : alph ≠ 0 := alph_pos.ne'
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

/-- `W x j = x^{α^{-j}}`. -/
noncomputable def W (x : ℝ) (j : ℕ) : ℝ := Real.exp (Real.log x / alph ^ j)

lemma W_alph (x : ℝ) (j : ℕ) : W x (j + 1) ^ alph = W x j := by
  unfold W
  rw [← Real.exp_mul, pow_succ, div_mul_eq_mul_div, mul_div_mul_right _ _ alph_pos.ne']

lemma W_zero {x : ℝ} (hx : 0 < x) : W x 0 = x := by
  unfold W; rw [pow_zero, div_one, Real.exp_log hx]

lemma one_le_W {x : ℝ} (hx : 1 ≤ x) (j : ℕ) : 1 ≤ W x j :=
  Real.one_le_exp (div_nonneg (Real.log_nonneg hx) (pow_pos alph_pos j).le)

lemma log_W (x : ℝ) (j : ℕ) : Real.log (W x j) = Real.log x / alph ^ j := Real.log_exp _

lemma cover {x M : ℝ} (hx : 1 ≤ x) (J : ℕ) (hJ : W x J ≤ M) (k : ℕ) (hk : M < k)
    (hkx : (k : ℝ) ≤ x) (hodd : Odd k) : ∃ j < J, k ∈ oddIcc (W x (j + 1)) := by
  classical
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · rw [h, W_zero (by linarith)] at hJ; linarith
    · exact h
  have hex : ∃ j, W x (j + 1) ≤ k :=
    ⟨J - 1, by rw [show J - 1 + 1 = J by omega]; linarith⟩
  obtain ⟨j, hj, hjmin⟩ : ∃ j, W x (j + 1) ≤ k ∧ ∀ i < j, ¬ W x (i + 1) ≤ k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjJ : j < J := by
    by_contra hcon
    exact hjmin (J - 1) (by omega) (by rw [show J - 1 + 1 = J by omega]; linarith)
  refine ⟨j, hjJ, ?_⟩
  unfold oddIcc
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨Nat.ceil_le.mpr hj, Nat.le_floor ?_⟩, hodd⟩
  rw [W_alph]
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, W_zero (by linarith)]; exact hkx
  · have := hjmin (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    exact (not_le.mp this).le

open Classical in
/-- Weight of `k` in interval `j`, restricted to the event `Q`. -/
noncomputable def G (x : ℝ) (Q : ℕ → Prop) (j k : ℕ) : ℝ :=
  if k ∈ oddIcc (W x (j + 1)) then (if Q k then (1 : ℝ) / k else 0) else 0

lemma G_nonneg (x : ℝ) (Q : ℕ → Prop) (j k : ℕ) : 0 ≤ G x Q j k := by
  unfold G; split_ifs <;> positivity

lemma G_sum_le (x : ℝ) (Q : ℕ → Prop) (j : ℕ) (R : Finset ℕ) :
    ∑ k ∈ R, G x Q j k ≤ Z (W x (j + 1)) * prob (W x (j + 1)) Q := by
  refine le_trans ?_ (num_le _ _)
  unfold G
  rw [Finset.sum_ite_mem]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun i _ _ => by split_ifs <;> positivity)

lemma log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- DECOMPOSE item 5e (main step): the leaf's bound for all large thresholds, from Prop 1.11. -/
theorem sec3_main (hP : Prop111) : ∃ C0 c M1 : ℝ, 0 < C0 ∧ 0 < c ∧ 3 ≤ M1 ∧
    ∀ M x : ℝ, M1 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C0 / Real.rpow (Real.log M) c := by
  obtain ⟨C', c, M0, hC', hc, hM0, hIB⟩ := interval_bound hP
  refine ⟨1002 * C', c, max M0 3, by positivity, hc, le_max_right _ _, ?_⟩
  intro M x hM hx
  have hM3 : (3 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have hMM0 : M0 ≤ M := le_trans (le_max_left _ _) hM
  have hlM : 1 < Real.log M :=
    lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) hM3)
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  set B := C' * Real.log M ^ (-c) with hBdef
  have hB : 0 ≤ B := mul_nonneg hC'.le (Real.rpow_nonneg (by linarith) _)
  have hgoal : 1002 * C' / Real.rpow (Real.log M) c = B * 1002 := by
    have h1 : Real.log M ^ (-c) = (Real.log M ^ c)⁻¹ := Real.rpow_neg (by linarith) c
    rw [hBdef, h1]
    show 1002 * C' / Real.log M ^ c = _
    ring
  rw [hgoal]
  unfold weightedLogMassReal
  rw [div_le_iff₀ hlx0]
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hkx : ∀ k ∈ Finset.range (⌊x⌋₊ + 1), (k : ℝ) ≤ x := by
    intro k hk
    have h3 : k ≤ ⌊x⌋₊ := by have := Finset.mem_range.mp hk; omega
    exact (Nat.cast_le.mpr h3).trans (Nat.floor_le (by linarith))
  by_cases hxM : x ≤ M
  · refine le_trans (Finset.sum_nonpos (fun k hk => ?_))
      (mul_nonneg (mul_nonneg hB (by norm_num)) hlx0.le)
    split_ifs with h
    · exfalso
      obtain ⟨_, hbad⟩ := h
      have hbad' : M < (syracuseOrbitMin k : ℝ) := hbad
      have h1 : (syracuseOrbitMin k : ℝ) ≤ k := by exact_mod_cast orbitMin_le_self k
      linarith [hkx k hk]
    · exact le_rfl
  push_neg at hxM
  have hlxM : Real.log M < Real.log x := Real.log_lt_log (by linarith) hxM
  set J := ⌈1000 * Real.log x⌉₊ with hJdef
  have hJx : 1000 * Real.log x ≤ J := Nat.le_ceil _
  have hJx' : (J : ℝ) < 1000 * Real.log x + 1 := Nat.ceil_lt_add_one (by linarith)
  have halph : alph = 1 + 1 / 1000 := by unfold alph; norm_num
  have hpowJ : 1 + Real.log x ≤ alph ^ J := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 1000 by norm_num) J
    rw [halph]; linarith
  have hWJ : W x J ≤ M := by
    unfold W
    rw [← Real.exp_log (by linarith : 0 < M)]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (pow_pos alph_pos J)]
    nlinarith
  refine le_trans (Finset.sum_le_sum (g := fun k => ∑ j ∈ Finset.range J,
    G x (fun N => M < (syracuseOrbitMin N : ℝ)) j k) (fun k hk => ?_)) ?_
  · split_ifs with h
    · obtain ⟨⟨_, hodd⟩, hbad⟩ := h
      have hbad' : M < (syracuseOrbitMin k : ℝ) := hbad
      have h1 : (syracuseOrbitMin k : ℝ) ≤ k := by exact_mod_cast orbitMin_le_self k
      obtain ⟨j, hj, hmem⟩ := cover hx1 J hWJ k (by linarith) (hkx k hk) hodd
      have hterm : G x (fun N => M < (syracuseOrbitMin N : ℝ)) j k = 1 / (k : ℝ) := by
        unfold G; rw [if_pos hmem, if_pos hbad']
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun i _ => G_nonneg _ _ i k)
        (Finset.mem_range.mpr hj))
      rw [hterm]
    · exact Finset.sum_nonneg (fun i _ => G_nonneg _ _ i k)
  · rw [Finset.sum_comm]
    have hj : ∀ j ∈ Finset.range J, ∑ k ∈ Finset.range (⌊x⌋₊ + 1),
        G x (fun N => M < (syracuseOrbitMin N : ℝ)) j k
          ≤ (1 + (alph - 1) * (Real.log x / alph ^ (j + 1))) * B := by
      intro j _
      refine le_trans (G_sum_le _ _ _ _) ?_
      have hprob := hIB M (W x (j + 1 + 1)) hMM0 (one_le_W hx1 _)
      rw [W_alph] at hprob
      have hZ := Z_le (one_le_W hx1 (j + 1))
      rw [log_W] at hZ
      calc Z (W x (j + 1)) * prob (W x (j + 1)) (fun N => M < (syracuseOrbitMin N : ℝ))
          ≤ Z (W x (j + 1)) * B := mul_le_mul_of_nonneg_left hprob (Z_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right hZ hB
    refine le_trans (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_mul]
    have hsum : ∑ j ∈ Finset.range J, (1 + (alph - 1) * (Real.log x / alph ^ (j + 1))) =
        J + Real.log x * (1 - 1 / alph ^ J) := by
      rw [Finset.sum_add_distrib, ← geom_alph J, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum]
    have ht : 0 ≤ Real.log x * (1 / alph ^ J) :=
      mul_nonneg hlx0.le (by have := pow_pos alph_pos J; positivity)
    have hE : (J : ℝ) + Real.log x * (1 - 1 / alph ^ J) ≤ 1002 * Real.log x := by
      have e : Real.log x * (1 - 1 / alph ^ J) = Real.log x - Real.log x * (1 / alph ^ J) := by
        ring
      rw [e]; linarith
    calc ((J : ℝ) + Real.log x * (1 - 1 / alph ^ J)) * B ≤ (1002 * Real.log x) * B :=
          mul_le_mul_of_nonneg_right hE hB
      _ = B * 1002 * Real.log x := by ring

/-- DECOMPOSE item 5e: the leaf statement from the Prop 1.11 interface. -/
theorem sec3 (hP : Prop111) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 3 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C / Real.rpow (Real.log M) c := by
  obtain ⟨C0, c, M1, hC0, hc, hM1, h⟩ := sec3_main hP
  exact reduce_large_M C0 c M1 hC0 hc hM1 h

/-- Def-free law of `N_y` (log-uniform odd integers in `[y, y^1.001]`). -/
def ProbEq (P : ℝ → (ℕ → Prop) → ℝ) : Prop :=
  ∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
    (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
        Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
      ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N

theorem prob_ProbEq : ProbEq prob := by
  classical
  intro y Q
  unfold prob Z oddIcc alph
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  all_goals first
    | rfl
    | (simp only [Finset.filter_congr_decidable])
    | (convert rfl)

theorem pass_iff (x : ℝ) (N : ℕ) (E : ℕ → Prop) :
    (Reaches x N ∧ E (Pass x N)) ↔
      ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧ (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧
        E (syracuseStep^[k] N) := by
  classical
  constructor
  · rintro ⟨h, hE⟩
    have hT : T x N = Nat.find h := by unfold T; rw [dif_pos h]
    refine ⟨Nat.find h, Nat.find_spec h, fun j hj => lt_of_not_ge (Nat.find_min h hj), ?_⟩
    unfold Pass at hE; rw [hT] at hE; exact hE
  · rintro ⟨k, hk, hmin, hE⟩
    have h : Reaches x N := ⟨k, hk⟩
    have hfk : Nat.find h = k := by
      apply le_antisymm (Nat.find_min' h hk)
      by_contra hlt
      exact absurd (Nat.find_spec h) (not_le.2 (hmin _ (lt_of_not_ge hlt)))
    refine ⟨h, ?_⟩
    have hT : T x N = k := by unfold T; rw [dif_pos h]; exact hfk
    unfold Pass; rw [hT]; exact hE

/-- Def-free Prop 1.11 (child statement body, `ProbEq` unfolded in the spec). -/
def Prop111_inl : Prop :=
  ∀ P : ℝ → (ℕ → Prop) → ℝ, ProbEq P →
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    P (x ^ ((1001 : ℝ) / 1000)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |P (x ^ ((1001 : ℝ) / 1000)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) -
        P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N))| ≤
        C * Real.log x ^ (-c)

theorem pass_fun (x : ℝ) (E : ℕ → Prop) :
    (fun N => Reaches x N ∧ E (Pass x N)) = (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
      (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) :=
  funext fun N => propext (pass_iff x N E)

theorem prop111_iff : Prop111 ↔ Prop111_inl := by
  constructor
  · rintro ⟨C, c, x0, hC, hc, hb⟩ P hP
    have hPp : P = prob := funext fun y => funext fun Q => (hP y Q).trans (prob_ProbEq y Q).symm
    subst hPp
    refine ⟨C, c, x0, hC, hc, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb x hx
    refine ⟨h1, h2, fun E => ?_⟩
    rw [← pass_fun]; exact h3 E
  · intro h
    obtain ⟨C, c, x0, hC, hc, hb⟩ := h prob prob_ProbEq
    refine ⟨C, c, x0, hC, hc, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb x hx
    refine ⟨h1, h2, fun E => ?_⟩
    have := h3 E
    rw [← pass_fun] at this
    exact this


/-- The renewal-process expectation `V r j l` of Tao Section 7, defined by its recursion. -/
noncomputable def Vd (n K : ℕ) (ξ : ℤ) (ε : ℝ) (r : ℕ) : ℕ → ℕ → ℝ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℝ) (fun _ _ => 1)
    (fun _ Vr j l => ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * Vr (j + 1) (l + ∑ i, u i)) r

/-- Tao Prop 1.17 (Fourier decay) from Prop 7.2 (`characteristic_function_le_renewal_expectation`)
and Prop 7.3 (`renewal_white_decay_of_black_triangle_case` applied to its Case 3). -/
theorem fourier_decay : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ C * (n : ℝ) ^ (-A) := by
  intro A hA
  have h2 := Tao2022Collatz.renewal_white_decay_of_black_triangle_case
    Tao2022Collatz.renewal_large_black_triangle_case
  obtain ⟨C, hC, hb⟩ := h2 (1 / 200) (by norm_num) (by norm_num) A hA
  refine ⟨C, hC, fun n K hn hnK ξ hξ => ?_⟩
  exact (Tao2022Collatz.characteristic_function_le_renewal_expectation n K ξ (1 / 200) (by norm_num)
    (by norm_num) (Vd n K ξ (1 / 200)) (fun _ _ => rfl) (fun _ _ _ => rfl)).trans
    (hb n K hn hnK ξ hξ (Vd n K ξ (1 / 200)) (fun _ _ => rfl) (fun _ _ _ => rfl))

/-- Tao Prop 1.11 from Prop 1.14 (`fine_scale_mixing_of_fourier_decay`) and the Section 5 children. -/
theorem prop111_holds : Prop111 := by
  apply prop111_iff.mpr
  exact Tao2022Collatz.first_passage_stabilisation_of_mixing
    Tao2022Collatz.syracuse_block_class_sum_bound Tao2022Collatz.valuation_law_and_tails
    Tao2022Collatz.section5_parameter_estimates
    (Tao2022Collatz.fine_scale_mixing_of_fourier_decay fourier_decay)

end Tao31

open Tao31 in
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 3 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C / Real.rpow (Real.log M) c := by
  exact sec3 prop111_holds
