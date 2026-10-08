-- Prove2me | solution 1 for odd_sum_le_973_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-04T18:06:06.536212+00:00
-- url     : https://prove2.me/submissions/62818964-b2c3-4630-9821-33a83bfc5a43

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_pi_lower
import Theorems.Thm_Schnir_sieve_ineq
import Theorems.Thm_Schnir_G_lower
import Theorems.Thm_Schnir_basis_of_density

/-!
Every odd `n > 1` is a sum of at most `973` primes.

Same elementary route as the proved `6101` entry, with three changes:
* the sieve bound is taken at the lower threshold `e^250`: `r(s) ≤ (21/2) C(s) s / log² s`,
  from the proved general `sieve_ineq` and `G_lower` with `z = √s / log² s`;
* a fourth moment `∑_{s ≤ x, s even} C(s)^4 ≤ 345 x` (Euler product, as in `C_mean`)
  and Hölder `(∑ f)^4 ≤ |F|^3 ∑ f^4` replace Cauchy–Schwarz, giving `R(n) ≥ n/600`
  for `n ≥ e^550`; with Chebyshev's bound for smaller `N` this gives `σ(A) ≥ 1/486`;
* Mann's theorem, via the proved `basis_of_density`, turns `486 σ(A) ≥ 1` into
  `486 A = ℕ`, so `972` odd primes plus one `3`: `K = 973`.
-/

open Finset Real

namespace Schnir

-- ===== part a: first moment =====


/-- odd primes `≤ t`. -/
def s6P (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

lemma s6_card_P (M : ℕ) (hM : 2 ≤ M) : (s6P M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : s6P M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [s6P, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

lemma s6_Q_lower (n t : ℕ) (hn : 1000 ≤ n) (ht : t ≤ n) :
    2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ (s6P t).card := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  by_cases h : t < 1000
  · have : ((t : ℝ) - 1000) ≤ 0 := by
      have : (t : ℝ) < 1000 := by exact_mod_cast h
      linarith
    have : 2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    exact this.trans (Nat.cast_nonneg _)
  · push Not at h
    have ht' : (1000 : ℝ) ≤ t := by exact_mod_cast h
    have hp := pi_lower t ht'
    rw [Nat.floor_natCast] at hp
    have hc := s6_card_P t (by omega)
    have hc' : ((s6P t).card : ℝ) = (Nat.primeCounting t : ℝ) - 1 := by
      rw [← hc]; push_cast; ring
    rw [hc']
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hle : Real.log t ≤ Real.log n := Real.log_le_log (by linarith) (by exact_mod_cast ht)
    have h1 : 2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ 2 * t / (3 * Real.log n) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h2 : 2 * (t : ℝ) / (3 * Real.log n) ≤ 2 * t / (3 * Real.log t) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith

/-- `∑_{s ≤ n} r s ≥ ∑_{p ∈ P(K)} Q(n - p)` for `K ≤ n`. -/
lemma s6_pairs (n K : ℕ) (hK : K ≤ n) :
    ∑ p ∈ s6P K, (s6P (n - p)).card ≤ ∑ s ∈ range (n + 1), r s := by
  unfold r
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun pq => (⟨pq.1 + pq.2, pq.1⟩ : Σ _ : ℕ, ℕ))
  · intro pq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, s6P, Finset.mem_filter, Finset.mem_range] at hpq ⊢
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hpq
    refine ⟨by omega, by omega, h2, h3, ?_, ?_⟩
    · rw [Nat.add_sub_cancel_left]; exact h5
    · rw [Nat.add_sub_cancel_left]; exact h6
  · intro a _ b _ hab
    simp only [Sigma.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have h2' : a.1 = b.1 := eq_of_heq h2
    exact Sigma.ext h2' (heq_of_eq (by omega))

lemma s6_Ico_card (p K : ℕ) : ((range K).filter (fun t => p ≤ t)).card = K - p := by
  have : (range K).filter (fun t => p ≤ t) = Ico p K := by
    ext t; simp [Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- `∑_{p ∈ P(K)} (K - p) = ∑_{t < K} Q(t)`. -/
lemma s6_swap (K : ℕ) : ∑ p ∈ s6P K, (K - p) = ∑ t ∈ range K, (s6P t).card := by
  have h1 : ∀ p ∈ s6P K, K - p = ∑ t ∈ range K, if p ≤ t then 1 else 0 := by
    intro p _
    rw [Finset.sum_boole, ← s6_Ico_card p K]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  congr 1
  ext p
  simp only [s6P, Finset.mem_filter, Finset.mem_range] at ht ⊢
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩

lemma s6_gauss (K : ℕ) : ∑ t ∈ range K, ((t : ℝ) - 1000) = (K : ℝ) * (K - 1) / 2 - 1000 * K := by
  induction K with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The lower function `L(t) = 2 (t - 1000)(t - 3001) / (9 (log t)^2)`. -/
noncomputable def s6L (t : ℝ) : ℝ := 2 * (t - 1000) * (t - 3001) / (9 * (Real.log t) ^ 2)

/-- Triangle first moment: `∑_{s ≤ n} r(s) ≥ L(n)` for `n ≥ 1000`. -/
theorem s6_first_moment (n : ℕ) (hn : 1000 ≤ n) :
    s6L n ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
  set K := n - 1000 with hKdef
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set c := 2 / (3 * Real.log n) with hc
  have hc0 : 0 ≤ c := by positivity
  have hK : (K : ℝ) = n - 1000 := by rw [hKdef]; push_cast [hn]; ring
  -- step 1
  have hstep1 : ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]; exact_mod_cast s6_pairs n K (by omega)
  -- step 2
  have hstep2 : c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) ≤ ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simp only [s6P, Finset.mem_filter, Finset.mem_range] at hp
    have := s6_Q_lower n (n - p) hn (by omega)
    have e : ((n - p : ℕ) : ℝ) - 1000 = ((K - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hK]; ring
    rw [e] at this; exact this
  -- step 3
  have hstep3 : ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) = ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, s6_swap]
  -- step 4
  have hstep4 : c * ∑ t ∈ range K, ((t : ℝ) - 1000) ≤ ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_range] at ht
    exact s6_Q_lower n t hn (by omega)
  rw [s6_gauss] at hstep4
  have hfin : s6L n = c * (c * ((K : ℝ) * (K - 1) / 2 - 1000 * K)) := by
    rw [s6L, hc, hK]; field_simp; ring
  rw [hfin]
  calc c * (c * ((K : ℝ) * (K - 1) / 2 - 1000 * K))
      ≤ c * ∑ t ∈ range K, ((s6P t).card : ℝ) := mul_le_mul_of_nonneg_left hstep4 hc0
    _ = c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) := by rw [hstep3]
    _ ≤ _ := hstep2.trans hstep1


-- ===== part b =====

/-- Summation by parts, as an inequality. -/
lemma s6_abel (a w L : ℕ → ℝ) (n0 : ℕ)
    (hw : ∀ k, n0 < k → w (k + 1) ≤ w k)
    (hML : ∀ k, n0 < k → L k ≤ ∑ s ∈ range (k + 1), a s) :
    ∀ n, n0 ≤ n →
      ∑ s ∈ Ioc n0 n, (L s - L (s - 1)) * w s
        + (∑ s ∈ range (n + 1), a s - L n) * w (n + 1)
        - (∑ s ∈ range (n0 + 1), a s - L n0) * w (n0 + 1)
      ≤ ∑ s ∈ Ioc n0 n, a s * w s := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ioc_succ_top hk, Finset.sum_Ioc_succ_top hk, Finset.sum_range_succ _ (k + 1)]
    have h1 := hML (k + 1) (by omega)
    have h2 := hw (k + 1) (by omega)
    rw [Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel] at ih ⊢
    have h3 : 0 ≤ (∑ s ∈ range (k + 1), a s + a (k + 1) - L (k + 1)) * (w (k + 1) - w (k + 1 + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Per-term bound: `(L(t) - L(t-1)) · (log t)^2 / t ≥ 0.4439` for `t ≥ e^1000`. -/
lemma s6_term (t : ℝ) (ht : Real.exp 250 ≤ t) :
    442 / 1000 ≤ (s6L t - s6L (t - 1)) * (Real.log t ^ 2 / t) := by
  have hbig : (10 : ℝ) ^ 9 ≤ t := by
    have h1 : (26 : ℝ) ≤ Real.exp 25 := by have := Real.add_one_le_exp (25 : ℝ); linarith
    have h2 : Real.exp 250 = Real.exp 25 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (26 : ℝ) ^ 10 ≤ Real.exp 25 ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
    nlinarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  set u := Real.log t with hu_def
  set v := Real.log (t - 1) with hv_def
  have hu : 250 ≤ u := by
    have := Real.log_le_log (Real.exp_pos 250) ht
    rwa [Real.log_exp] at this
  have hvu : v ≤ u := Real.log_le_log ht1 (by linarith)
  have huv : u - v ≤ 1 / (t - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / (t - 1) by positivity)
    rw [Real.log_div (by linarith) ht1.ne'] at h
    have : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  have hinv : 1 / (t - 1) ≤ 1 / 1000 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hv : 249 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  -- u^2 - v^2 ≤ 2u/(t-1)
  have hsq : u ^ 2 - v ^ 2 ≤ 2 * u / (t - 1) := by
    have : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [this]
    calc (u - v) * (u + v) ≤ 1 / (t - 1) * (u + v) :=
          mul_le_mul_of_nonneg_right huv (by linarith)
      _ ≤ 1 / (t - 1) * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * u / (t - 1) := by ring
  -- u / v^2 ≤ 1/240
  have huv2 : u / v ^ 2 ≤ 1 / 240 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- u^2 / v^2 ≤ 1 + (2/990)/(t-1)
  have hratio : u ^ 2 / v ^ 2 ≤ 1 + 2 / 240 / (t - 1) := by
    have e : u ^ 2 / v ^ 2 = 1 + (u ^ 2 - v ^ 2) / v ^ 2 := by field_simp; ring
    rw [e]
    have : (u ^ 2 - v ^ 2) / v ^ 2 ≤ 2 * u / (t - 1) / v ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e2 : 2 * u / (t - 1) / v ^ 2 = 2 * (u / v ^ 2) / (t - 1) := by field_simp
    have : 2 * (u / v ^ 2) / (t - 1) ≤ 2 * (1 / 240) / (t - 1) :=
      div_le_div_of_nonneg_right (by linarith) ht1.le
    have e3 : 2 * (1 / 240) / (t - 1) = 2 / 240 / (t - 1) := by ring
    linarith
  -- f(t-1) bounds
  set g := (t - 1 - 1000) * (t - 1 - 3001) with hg
  have hg0 : 0 ≤ g := by rw [hg]; apply mul_nonneg <;> linarith
  have hgle : g ≤ (t - 1) ^ 2 := by rw [hg]; nlinarith
  have hexp : (s6L t - s6L (t - 1)) * (u ^ 2 / t)
      = 2 / 9 * ((t - 1000) * (t - 3001) - g * (u ^ 2 / v ^ 2)) / t := by
    rw [s6L, s6L, ← hu_def, ← hv_def, hg]
    field_simp
  rw [hexp]
  have hgr : g * (u ^ 2 / v ^ 2) ≤ g + 2 / 240 * (t - 1) := by
    calc g * (u ^ 2 / v ^ 2) ≤ g * (1 + 2 / 240 / (t - 1)) := mul_le_mul_of_nonneg_left hratio hg0
      _ = g + 2 / 240 * (g / (t - 1)) := by ring
      _ ≤ g + 2 / 240 * (t - 1) := by
        have : g / (t - 1) ≤ t - 1 := by
          rw [div_le_iff₀ ht1]; nlinarith
        linarith
  rw [le_div_iff₀ (by linarith)]
  have e4 : (t - 1000) * (t - 3001) = g + 2 * t - 4002 := by rw [hg]; ring
  rw [e4]
  nlinarith



-- ===== part c =====

theorem s6_r_le (s : ℕ) : r s ≤ s := by
  unfold r
  calc _ ≤ (Finset.Icc 1 s).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        have := hp.2.1.one_lt
        simp only [Finset.mem_Icc]; omega
    _ = s := by simp

theorem s6_r_odd (s : ℕ) (hs : ¬ Even s) : r s = 0 := by
  unfold r
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ⟨hpp, hp2, hqp, hq2⟩
  simp only [Finset.mem_range] at hp
  have h1 := hpp.odd_of_ne_two hp2
  have h2 := hqp.odd_of_ne_two hq2
  have : Even (p + (s - p)) := Odd.add_odd h1 h2
  rw [Nat.add_sub_cancel' (by omega)] at this
  exact hs this

theorem s6_mono (a b : ℝ) (ha : 250 ≤ a) (hab : a ≤ b) :
    Real.exp a / a ^ 2 ≤ Real.exp b / b ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : b ≤ a * (1 + (b - a) / 2) := by nlinarith
  have h2 : 1 + (b - a) / 2 ≤ Real.exp ((b - a) / 2) := by
    have := Real.add_one_le_exp ((b - a) / 2); linarith
  have h3 : b ≤ a * Real.exp ((b - a) / 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 ha0.le)
  have h4 : b ^ 2 ≤ a ^ 2 * Real.exp (b - a) := by
    have : Real.exp (b - a) = Real.exp ((b - a) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ hb0.le h3 2
  have h5 : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h5]
  have := Real.exp_pos a
  nlinarith

/-- The weight `(log t)^2 / t` decreases past `e^250`. -/
theorem s6_w_anti (k : ℝ) (hk : Real.exp 250 ≤ k) :
    Real.log (k + 1) ^ 2 / (k + 1) ≤ Real.log k ^ 2 / k := by
  have hk0 : 0 < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hu : 250 ≤ Real.log k := by
    have := Real.log_le_log (Real.exp_pos 250) hk
    rwa [Real.log_exp] at this
  have huv : Real.log k ≤ Real.log (k + 1) := Real.log_le_log hk0 (by linarith)
  have h := s6_mono _ _ hu huv
  rw [Real.exp_log hk0, Real.exp_log (by linarith)] at h
  have hv : 0 < Real.log (k + 1) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h ⊢
  linarith


-- ===== sieve bound at e^250 =====

/-- Pairs counted by `r s` either have a small prime or are counted by `S s z`. -/
theorem n9_r_le_S (s : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (r s : ℝ) ≤ S s z + 2 * z := by
  have hsub : (Finset.range (s + 1)).filter
      (fun p => p.Prime ∧ p ≠ 2 ∧ (s - p).Prime ∧ s - p ≠ 2) ⊆
      (Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪
      (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hps, hpp, -, hqp, -⟩ := hp
    have hp1 := hpp.one_lt
    have hq1 := hqp.one_lt
    by_cases h1 : p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_Icc]; left; left; omega
    by_cases h2 : s - p ≤ ⌊z⌋₊
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]; left; right
      exact ⟨s - p, ⟨by omega, h2⟩, by omega⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    right
    refine ⟨⟨by omega, by omega⟩, fun q hq hqpr hdvd => ?_⟩
    rcases (Nat.Prime.dvd_mul hqpr).1 hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hpp).1 h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hqpr hqp).1 h; omega
  set T := (Finset.Icc 1 s).filter
        (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a)) with hT
  have hcard := Finset.card_le_card hsub
  have h3 : ((Finset.Icc 1 ⌊z⌋₊ ∪ (Finset.Icc 1 ⌊z⌋₊).image (fun q => s - q)) ∪ T).card
      ≤ ⌊z⌋₊ + ⌊z⌋₊ + T.card := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans ?_
    have := (Finset.card_image_le (s := Finset.Icc 1 ⌊z⌋₊) (f := fun q => s - q))
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this ⊢
    omega
  have h4 := hcard.trans h3
  have h5 : (r s : ℝ) ≤ (⌊z⌋₊ : ℝ) + ⌊z⌋₊ + S s z := by
    unfold r S; exact_mod_cast h4
  have h6 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  linarith

/-- `C s ≥ 3` for even `s`. -/
theorem n9_C_ge_three (s : ℕ) (hs : Even s) (hs0 : 0 < s) : 3 ≤ C s := by
  unfold C
  have h2 : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hs, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h2]
  have hrest : (1 : ℝ) ≤ ∏ p ∈ s.primeFactors.erase 2, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    calc (1 : ℝ) = ∏ p ∈ s.primeFactors.erase 2, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intros; norm_num
        · intro p _
          have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
          linarith
  norm_num
  linarith

/-- `log L ≤ L / 40` for `L ≥ 250`. -/
theorem n9_log_le (L : ℝ) (hL : 250 ≤ L) : Real.log L ≤ L / 40 := by
  have h6 : Real.log 250 < 6 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (250 : ℝ) < 2.7182818283 ^ 6 := by norm_num
      _ < Real.exp 1 ^ 6 := by gcongr
  have h1 : Real.log (L / 250) ≤ L / 250 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  linarith

/-- Sieve bound at the lower threshold `e^250`: `r(s) ≤ (21/2) C(s) s / log² s`. -/
theorem n9_pointwise (s : ℕ) (hs : Even s) (hbig : Real.exp 250 ≤ s) :
    (r s : ℝ) ≤ 21 / 2 * C s * s / (Real.log s) ^ 2 := by
  have hs1 : (251 : ℝ) ≤ s := by
    have := Real.add_one_le_exp 250; linarith
  have hs0 : 0 < s := by exact_mod_cast (show (0:ℝ) < s by linarith)
  have hspos : (0 : ℝ) < s := by linarith
  set L := Real.log s with hLdef
  have hL : 250 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 250) hbig
    rwa [Real.log_exp] at this
  have hLpos : 0 < L := by linarith
  have hlogL := n9_log_le L hL
  have hlogL' : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hLpos]
    have := Real.exp_one_lt_d9; linarith
  set z := √(s : ℝ) / L ^ 2 with hzdef
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.2 hspos
  have hzpos : 0 < z := by positivity
  have hlogz : Real.log z = L / 2 - 2 * Real.log L := by
    rw [hzdef, Real.log_div hsq.ne' (by positivity), Real.log_sqrt hspos.le, Real.log_pow]
    push_cast; ring
  have hlz1 : 9 / 20 * L ≤ Real.log z := by rw [hlogz]; linarith
  have hlz2 : 1 + Real.log z ≤ L / 2 := by rw [hlogz]; linarith
  have hz1 : 1 < z := by
    have : 0 < Real.log z := by linarith
    exact (Real.log_pos_iff hzpos.le).1 this
  have hC := n9_C_ge_three s hs hs0
  have hSi := sieve_ineq s hs hs0 z hz1
  have hG := G_lower s hs hs0 z hz1
  have hrS := n9_r_le_S s z hzpos.le
  have hlzpos : 0 < Real.log z := by linarith
  have hGpos : 0 < G s z := lt_of_lt_of_le (by positivity) hG
  -- s / G ≤ 2 C s / (log z)^2 ≤ 625/72 * C s / L^2
  have hA : (s : ℝ) / G s z ≤ 800 / 81 * C s * s / L ^ 2 := by
    rw [div_le_div_iff₀ hGpos (by positivity)]
    have h1 : (Real.log z) ^ 2 ≤ 2 * C s * G s z := by
      rw [div_le_iff₀ (by positivity)] at hG; linarith
    have h2 : 81 / 400 * L ^ 2 ≤ (Real.log z) ^ 2 := by nlinarith
    have : L ^ 2 ≤ 800 / 81 * C s * G s z := by nlinarith
    nlinarith
  have hzsq : z ^ 2 = s / L ^ 4 := by
    rw [hzdef, div_pow, Real.sq_sqrt hspos.le]; ring
  have hB : z ^ 2 * (1 + Real.log z) ^ 2 ≤ s / (4 * L ^ 2) := by
    rw [hzsq]
    have h0 : 0 ≤ 1 + Real.log z := by linarith
    have : (1 + Real.log z) ^ 2 ≤ (L / 2) ^ 2 := by gcongr
    calc (s : ℝ) / L ^ 4 * (1 + Real.log z) ^ 2 ≤ s / L ^ 4 * (L / 2) ^ 2 := by gcongr
      _ = s / (4 * L ^ 2) := by field_simp; ring
  have h8 : 8 ≤ √(s : ℝ) := by
    rw [show (8 : ℝ) = √64 by rw [show (64:ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hD : 2 * z ≤ s / (4 * L ^ 2) := by
    rw [← sub_nonneg]
    have hss : (s : ℝ) = √(s:ℝ) * √(s:ℝ) := (Real.mul_self_sqrt hspos.le).symm
    have : (s : ℝ) / (4 * L ^ 2) - 2 * z = √(s:ℝ) * (√(s:ℝ) - 8) / (4 * L ^ 2) := by
      rw [hzdef]; nth_rewrite 1 [hss]; field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg hsq.le; linarith
  have hfin : (800 / 81 * C s * s / L ^ 2) + s / (4 * L ^ 2) + s / (4 * L ^ 2)
      ≤ 21 / 2 * C s * s / L ^ 2 := by
    rw [← sub_nonneg]
    have : 21 / 2 * C s * s / L ^ 2 - ((800 / 81 * C s * s / L ^ 2) + s / (4 * L ^ 2)
      + s / (4 * L ^ 2)) = (101 / 162 * C s - 1 / 2) * s / L ^ 2 := by field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg _ hspos.le
    linarith
  linarith
-- ===== fourth moment of C =====

noncomputable def c4_b (p : ℕ) : ℝ := ((1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 4 - 1) / p

lemma c4_b_nonneg (p : ℕ) : 0 ≤ c4_b p := by
  unfold c4_b
  apply div_nonneg _ (Nat.cast_nonneg _)
  have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
  have : 1 ≤ (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 4 := one_le_pow₀ (by linarith)
  linarith

lemma c4_b_le (p : ℕ) (hp : 11 ≤ p) :
    c4_b p ≤ 5 * (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold c4_b
  have h : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ) - 1 with hqdef
  have hpq : (p : ℝ) = q + 1 := by rw [hqdef]; ring
  rw [hpq]
  have hq10 : (10 : ℝ) ≤ q := by linarith
  rw [div_le_iff₀ (by linarith)]
  have e : (1 + (q + 1) / q ^ 2) ^ 4 - 1 = ((q ^ 2 + q + 1) ^ 4 - q ^ 8) / q ^ 8 := by
    field_simp; ring
  rw [e, show 5 * (1 / q ^ 2) * (q + 1) = (5 * (q + 1) * q ^ 6) / q ^ 8 by
    field_simp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  obtain ⟨d, hd, hqd⟩ : ∃ d, 0 ≤ d ∧ q = d + 10 := ⟨q - 10, by linarith, by ring⟩
  rw [hqd]
  ring_nf
  nlinarith [pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5, pow_nonneg hd 6,
    pow_nonneg hd 7]

lemma c4_tail (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p ∧ 11 ≤ p) :
    ∀ m : ℕ, 9 ≤ m → (∀ p ∈ Q, p ≤ m) →
      ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 18 - 1 / (2 * (m : ℝ)) := by
  induction Q using Finset.induction_on_max with
  | empty =>
    intro m hm _
    have : (9 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [sum_empty]
    rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  | insert a s hlt ih =>
    intro m hm hle
    have ha := hQ a (mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert has]
    have ih' := ih (fun p hp => hQ p (mem_insert_of_mem hp)) (a - 2) (by omega) (by
      intro p hp
      have h1 := hlt p hp
      have h2 := (hQ p (mem_insert_of_mem hp)).1
      obtain ⟨k, hk⟩ := h2
      obtain ⟨j, hj⟩ := ha.1
      omega)
    have hcast : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at ih'
    have haR : (11 : ℝ) ≤ a := by exact_mod_cast ha.2
    have hma : (a : ℝ) ≤ m := by exact_mod_cast hle a (mem_insert_self a s)
    have key : 1 / ((a : ℝ) - 1) ^ 2 ≤ 1 / (2 * ((a : ℝ) - 2)) - 1 / (2 * (a : ℝ)) := by
      rw [div_sub_div _ _ (by nlinarith) (by nlinarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    have hm2 : 1 / (2 * (m : ℝ)) ≤ 1 / (2 * (a : ℝ)) := by
      apply one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

lemma c4_exp_le (t : ℝ) (ht : t < 1) : exp t ≤ 1 / (1 - t) := by
  have h := Real.add_one_le_exp (-t)
  rw [le_div_iff₀ (by linarith)]
  have : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

lemma c4_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ P, (1 + c4_b p) ≤ 17 / 2 := by
  set Q := P.filter (fun p => 11 ≤ p) with hQdef
  have hsub : P ⊆ ({3, 5, 7} : Finset ℕ) ∪ Q := by
    intro p hp
    obtain ⟨hpr, hp2⟩ := hP p hp
    by_cases h : 11 ≤ p
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
    · apply mem_union_left
      have := hpr.two_le
      interval_cases p <;> first | (simp; done) | exact absurd rfl hp2 | norm_num at hpr
  have hdisj : Disjoint ({3, 5, 7} : Finset ℕ) Q := by
    rw [Finset.disjoint_left]
    intro a ha haQ
    have := (mem_filter.1 haQ).2
    simp at ha; omega
  have h1 : ∏ p ∈ P, (1 + c4_b p) ≤ ∏ p ∈ ({3, 5, 7} : Finset ℕ) ∪ Q, (1 + c4_b p) :=
    prod_le_prod_of_subset_of_one_le hsub (fun i _ => by linarith [c4_b_nonneg i])
      (fun i _ _ => by linarith [c4_b_nonneg i])
  rw [prod_union hdisj] at h1
  have h357 : ∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 + c4_b p) ≤ 607 / 100 := by
    simp [c4_b]; norm_num
  have hQodd : ∀ p ∈ Q, Odd p ∧ 11 ≤ p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(hP p hp1).1.odd_of_ne_two (hP p hp1).2, hp2⟩
  have hsum : ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 18 := by
    have := c4_tail Q hQodd (max 9 (Q.sup id)) (le_max_left _ _)
      (fun p hp => le_max_of_le_right (le_sup (f := id) hp))
    have h9 : (0 : ℝ) ≤ 1 / (2 * ((max 9 (Q.sup id) : ℕ) : ℝ)) := by positivity
    linarith
  have hbsum : ∑ p ∈ Q, c4_b p ≤ 5 / 18 := by
    calc ∑ p ∈ Q, c4_b p ≤ ∑ p ∈ Q, 5 * (1 / ((p : ℝ) - 1) ^ 2) :=
          sum_le_sum (fun p hp => c4_b_le p (hQodd p hp).2)
      _ = 5 * ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
      _ ≤ 5 * (1 / 18) := by gcongr
      _ = 5 / 18 := by norm_num
  have hQprod : ∏ p ∈ Q, (1 + c4_b p) ≤ 1 / (1 - 5 / 18) := by
    calc ∏ p ∈ Q, (1 + c4_b p) ≤ exp (∑ p ∈ Q, c4_b p) :=
          Real.prod_one_add_le_exp_sum Q c4_b_nonneg
      _ ≤ exp (5 / 18) := exp_le_exp.2 hbsum
      _ ≤ 1 / (1 - 5 / 18) := c4_exp_le _ (by norm_num)
  have hQ1 : 0 ≤ ∏ p ∈ Q, (1 + c4_b p) := prod_nonneg (fun i _ => by linarith [c4_b_nonneg i])
  calc ∏ p ∈ P, (1 + c4_b p)
      ≤ (∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 + c4_b p)) * ∏ p ∈ Q, (1 + c4_b p) := h1
    _ ≤ 607 / 100 * (1 / (1 - 5 / 18)) := by gcongr
    _ ≤ 17 / 2 := by norm_num


lemma c4_card (N : ℕ) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ p ≠ 2) :
    (((Icc 1 N).filter Even).filter (fun s => ∀ p ∈ U, p ∣ s)).card
      ≤ N / (2 * ∏ p ∈ U, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card
  intro s hs
  simp only [mem_filter, mem_Icc, mem_Ioc] at hs ⊢
  obtain ⟨⟨⟨h1, h2⟩, hev⟩, hdiv⟩ := hs
  refine ⟨⟨by omega, h2⟩, ?_⟩
  have h2U : (2 : ℕ) ∉ U := fun h => (hU 2 h).2 rfl
  have : 2 * ∏ p ∈ U, p = ∏ p ∈ insert 2 U, p := by rw [prod_insert h2U]
  rw [this]
  apply Finset.prod_primes_dvd
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Nat.prime_iff.1 (hU a ha).1
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact even_iff_two_dvd.1 hev
    · exact hdiv a ha

lemma c4_mul_b (p : ℕ) (hp : p ≠ 0) :
    (p : ℝ) * c4_b p = (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 4 - 1 := by
  unfold c4_b
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp

lemma c4_pointwise (N s : ℕ) (hs : s ∈ (Icc 1 N).filter Even) :
    C s ^ 4 = 81 * ∑ U ∈ ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).powerset,
      if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0 := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  simp only [mem_filter, mem_Icc] at hs
  obtain ⟨⟨h1, h2⟩, hev⟩ := hs
  have hs0 : s ≠ 0 := by omega
  have h2s : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hev, hs0⟩
  unfold C
  rw [← prod_pow, ← mul_prod_erase _ _ h2s]
  congr 1
  · norm_num
  simp_rw [← prod_ite_zero]
  rw [← prod_one_add]
  have hset : s.primeFactors.erase 2 = P.filter (fun p => p ∣ s) := by
    ext p
    simp only [mem_erase, Nat.mem_primeFactors, mem_filter, P, mem_range]
    constructor
    · rintro ⟨hp2, hpr, hdvd, -⟩
      exact ⟨⟨by have := Nat.le_of_dvd (by omega) hdvd; omega, hpr, hp2⟩, hdvd⟩
    · rintro ⟨⟨-, hpr, hp2⟩, hdvd⟩
      exact ⟨hp2, hpr, hdvd, hs0⟩
  rw [hset, prod_filter]
  apply prod_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := (mem_filter.1 hp).2.1.ne_zero
  split_ifs
  · rw [c4_mul_b p hp0]; ring
  · simp

/-- Fourth moment: `∑_{s ≤ x, s even} C(s)^4 ≤ 345 x`. -/
theorem c4_mean (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (C s) ^ 4 ≤ 345 * x := by
  set N := ⌊x⌋₊
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.1 hp).2
  set E := (Icc 1 N).filter Even
  rw [sum_congr rfl (fun s hs => c4_pointwise N s hs), ← mul_sum, sum_comm]
  have hterm : ∀ U ∈ P.powerset,
      ∑ s ∈ E, (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0)
        ≤ x / 2 * ∏ p ∈ U, c4_b p := by
    intro U hU
    have hUP : ∀ p ∈ U, p.Prime ∧ p ≠ 2 := fun p hp => hP p (mem_powerset.1 hU hp)
    rw [← sum_filter, sum_const, nsmul_eq_mul, prod_mul_distrib]
    have hc := c4_card N U hUP
    have hpos : (0 : ℝ) < ∏ p ∈ U, (p : ℝ) :=
      prod_pos (fun p hp => by exact_mod_cast (hUP p hp).1.pos)
    have hc' : ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
      calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ)
          ≤ ((N / (2 * ∏ p ∈ U, p) : ℕ) : ℝ) := by exact_mod_cast hc
        _ ≤ (N : ℝ) / ((2 * ∏ p ∈ U, p : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
          push_cast
          gcongr
          exact Nat.floor_le hx
    have hb : 0 ≤ ∏ p ∈ U, c4_b p := prod_nonneg (fun p _ => c4_b_nonneg p)
    calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, c4_b p)
        ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, c4_b p) := by
          gcongr
      _ = x / 2 * ∏ p ∈ U, c4_b p := by field_simp
  calc 81 * ∑ U ∈ P.powerset, ∑ s ∈ E,
        (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * c4_b p) else 0)
      ≤ 81 * ∑ U ∈ P.powerset, x / 2 * ∏ p ∈ U, c4_b p := by
        gcongr with U hU; exact hterm U hU
    _ = 81 * (x / 2) * ∏ p ∈ P, (1 + c4_b p) := by
        rw [prod_one_add, mul_sum, mul_sum]; simp only [mul_assoc]
    _ ≤ 81 * (x / 2) * (17 / 2) := by gcongr; exact c4_prod P hP
    _ ≤ 345 * x := by nlinarith

-- ===== weighted first moment and support bound =====

theorem s6_exp300 : (10 : ℝ) ^ 20 ≤ Real.exp 300 := by
  have h1 : (16 : ℝ) ≤ Real.exp 15 := by have := Real.add_one_le_exp (15 : ℝ); linarith
  have h2 : Real.exp 300 = Real.exp 15 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (16 : ℝ) ^ 20 ≤ Real.exp 15 ^ 20 := pow_le_pow_left₀ (by norm_num) h1 20
  have h4 : (10 : ℝ) ^ 20 ≤ 16 ^ 20 := by norm_num
  linarith

theorem s6_exp250 : (10 : ℝ) ^ 4 ≤ Real.exp 250 := by
  have h1 : (26 : ℝ) ≤ Real.exp 25 := by have := Real.add_one_le_exp (25 : ℝ); linarith
  have h2 : Real.exp 250 = Real.exp 25 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (26 : ℝ) ^ 10 ≤ Real.exp 25 ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
  have h4 : (10 : ℝ) ^ 4 ≤ 26 ^ 10 := by norm_num
  linarith

/-- Weighted first moment: `W(n) ≥ 0.44 n` for `n ≥ e^550`. -/
theorem s6_W (n : ℕ) (hn : Real.exp 550 ≤ n) :
    44 / 100 * (n : ℝ) ≤ ∑ s ∈ Ioc ⌊Real.exp 250⌋₊ n, (r s : ℝ) * (Real.log s ^ 2 / s) := by
  set n0 := ⌊Real.exp 250⌋₊ with hn0def
  have hE := s6_exp250
  have hE3 := s6_exp300
  have hn0 : (n0 : ℝ) ≤ Real.exp 250 := Nat.floor_le (Real.exp_pos _).le
  have hn0' : Real.exp 250 < n0 + 1 := Nat.lt_floor_add_one _
  have hexp2 : Real.exp 550 = Real.exp 250 * Real.exp 300 := by
    rw [← Real.exp_add]; norm_num
  have hn1 : (n : ℝ) ≥ 10 ^ 20 * Real.exp 250 := by
    have := Real.exp_pos 250
    nlinarith
  have hnn0 : n0 ≤ n := by
    have : (n0 : ℝ) ≤ n := by nlinarith [Real.exp_pos 250]
    exact_mod_cast this
  have hbig : ∀ k : ℕ, n0 < k → Real.exp 250 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have habel := s6_abel (fun s => (r s : ℝ)) (fun s => Real.log s ^ 2 / s) (fun s => s6L s) n0
    (by
      intro k hk
      have := s6_w_anti k (hbig k hk)
      push_cast; exact this)
    (by
      intro k hk
      have h1 := hbig k hk
      have : (1000 : ℝ) ≤ k := by linarith
      exact s6_first_moment k (by exact_mod_cast this))
    n hnn0
  -- (i) main sum
  have hi : 442 / 1000 * ((n : ℝ) - n0) ≤
      ∑ s ∈ Ioc n0 n, (s6L s - s6L ((s - 1 : ℕ) : ℝ)) * (Real.log s ^ 2 / s) := by
    have hcard : ((Ioc n0 n).card : ℝ) = (n : ℝ) - n0 := by
      rw [Nat.card_Ioc, Nat.cast_sub hnn0]
    rw [← hcard, mul_comm, ← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro s hs
    simp only [Finset.mem_Ioc] at hs
    have h1 := hbig s hs.1
    have : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    exact s6_term s h1
  -- (ii) the end term is nonnegative
  have hii : 0 ≤ (∑ s ∈ range (n + 1), (r s : ℝ) - s6L n) * (Real.log ((n + 1 : ℕ) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
    apply mul_nonneg
    · have h1 := hbig n (by
        by_contra h; push Not at h
        have : n = n0 := le_antisymm h hnn0
        rw [this] at hn; nlinarith [Real.exp_pos 250])
      have : (1000 : ℝ) ≤ n := by linarith
      have := s6_first_moment n (by exact_mod_cast this)
      linarith
    · positivity
  -- (iii) the start term is small
  have hiii : (∑ s ∈ range (n0 + 1), (r s : ℝ) - s6L n0) * (Real.log ((n0 + 1 : ℕ) : ℝ) ^ 2 / ((n0 + 1 : ℕ) : ℝ))
      ≤ 2 * 251 ^ 2 * Real.exp 250 := by
    have hn0big : (3001 : ℝ) ≤ n0 := by
      have : (3002 : ℝ) ≤ Real.exp 250 := by nlinarith
      have : (3002 : ℝ) < n0 + 1 := by linarith
      have : (3002 : ℕ) < n0 + 1 := by exact_mod_cast this
      exact_mod_cast (show 3001 ≤ n0 by omega)
    have hL0 : 0 ≤ s6L n0 := by
      unfold s6L
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    have hM0 : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ ((n0 : ℝ) + 1) ^ 2 := by
      have : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ (range (n0 + 1)).card • ((n0 : ℝ) + 1) := by
        apply Finset.sum_le_card_nsmul
        intro s hs
        simp only [Finset.mem_range] at hs
        have : r s ≤ n0 + 1 := (s6_r_le s).trans (by omega)
        exact_mod_cast this
      rw [Finset.card_range, nsmul_eq_mul] at this
      push_cast at this; nlinarith
    push_cast
    set m := (n0 : ℝ) + 1 with hm
    have hm0 : 0 < m := by linarith
    have hlogm : Real.log m ≤ 251 := by
      rw [Real.log_le_iff_le_exp hm0]
      have : Real.exp 251 = Real.exp 250 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      nlinarith
    have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
    have hw0 : 0 ≤ Real.log m ^ 2 / m := by positivity
    calc (∑ s ∈ range (n0 + 1), (r s : ℝ) - s6L n0) * (Real.log m ^ 2 / m)
        ≤ m ^ 2 * (Real.log m ^ 2 / m) := mul_le_mul_of_nonneg_right (by linarith) hw0
      _ = m * Real.log m ^ 2 := by field_simp
      _ ≤ (2 * Real.exp 250) * 251 ^ 2 := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ hlogm0 hlogm 2) (by positivity) (by positivity)
      _ = 2 * 251 ^ 2 * Real.exp 250 := by ring
  push_cast at hii hiii habel
  nlinarith

/-- `(∑ f)^4 ≤ |F|^3 ∑ f^4` (Cauchy–Schwarz twice). -/
theorem n9_holder (F : Finset ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ F, f s) ^ 4 ≤ (F.card : ℝ) ^ 3 * ∑ s ∈ F, f s ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := F) (f := f)
  have h2 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun s => f s ^ 2)
  have h0 : 0 ≤ (∑ s ∈ F, f s) ^ 2 := sq_nonneg _
  have h3 : ((∑ s ∈ F, f s) ^ 2) ^ 2 ≤ ((F.card : ℝ) * ∑ s ∈ F, f s ^ 2) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have e1 : (∑ s ∈ F, f s) ^ 4 = ((∑ s ∈ F, f s) ^ 2) ^ 2 := by ring
  have e2 : ∑ s ∈ F, f s ^ 4 = ∑ s ∈ F, (f s ^ 2) ^ 2 := by
    apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2]
  calc ((∑ s ∈ F, f s) ^ 2) ^ 2 ≤ ((F.card : ℝ) * ∑ s ∈ F, f s ^ 2) ^ 2 := h3
    _ = (F.card : ℝ) ^ 2 * (∑ s ∈ F, f s ^ 2) ^ 2 := by ring
    _ ≤ (F.card : ℝ) ^ 2 * ((F.card : ℝ) * ∑ s ∈ F, (f s ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- Support bound: `R(n) ≥ n / 600` for `n ≥ e^550`. -/
theorem n9_R (n : ℕ) (hn : Real.exp 550 ≤ n) :
    (n : ℝ) / 600 ≤ (((range (n + 1)).filter (fun s => 0 < r s)).card : ℝ) := by
  set n0 := ⌊Real.exp 250⌋₊ with hn0def
  have hn0' : Real.exp 250 < n0 + 1 := Nat.lt_floor_add_one _
  have hbig : ∀ k : ℕ, n0 < k → Real.exp 250 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hW := s6_W n hn
  set F := (Ioc n0 n).filter (fun s => 0 < r s) with hF
  set R := (range (n + 1)).filter (fun s => 0 < r s) with hR
  have hWF : ∑ s ∈ Ioc n0 n, (r s : ℝ) * (Real.log s ^ 2 / s)
      = ∑ s ∈ F, (r s : ℝ) * (Real.log s ^ 2 / s) := by
    rw [hF, Finset.sum_filter_of_ne]
    intro s _ h
    by_contra h'
    push Not at h'
    have : r s = 0 := by omega
    simp [this] at h
  have hH := n9_holder F (fun s => (r s : ℝ) * (Real.log s ^ 2 / s))
  have hterm : ∀ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 ≤ (21 / 2) ^ 4 * C s ^ 4 := by
    intro s hs
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
    have heven : Even s := by
      by_contra h
      have := s6_r_odd s h
      omega
    have h1 := hbig s hs.1.1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (Real.exp_pos _) h1
    have hlog : 0 < Real.log s := Real.log_pos (by nlinarith [Real.add_one_le_exp (250 : ℝ)])
    have hpb := n9_pointwise s heven h1
    have hup : (r s : ℝ) * (Real.log s ^ 2 / s) ≤ 21 / 2 * C s := by
      have hw : 0 < Real.log s ^ 2 / s := by positivity
      calc (r s : ℝ) * (Real.log s ^ 2 / s) ≤ 21 / 2 * C s * s / Real.log s ^ 2 * (Real.log s ^ 2 / s) :=
            mul_le_mul_of_nonneg_right hpb hw.le
        _ = 21 / 2 * C s := by field_simp
    have hlo : 0 ≤ (r s : ℝ) * (Real.log s ^ 2 / s) := by positivity
    calc ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 ≤ (21 / 2 * C s) ^ 4 := pow_le_pow_left₀ hlo hup 4
      _ = (21 / 2) ^ 4 * C s ^ 4 := by ring
  have hsumC : ∑ s ∈ F, C s ^ 4 ≤ 345 * (n : ℝ) := by
    have := c4_mean (n : ℝ) (Nat.cast_nonneg n)
    rw [Nat.floor_natCast] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hs.1.2⟩, ?_⟩
      by_contra h
      have := s6_r_odd s h
      omega
    · intros; positivity
  have hFR : F.card ≤ R.card := by
    apply Finset.card_le_card
    intro s hs
    simp only [hF, hR, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hs ⊢
    exact ⟨by omega, hs.2⟩
  have hFR' : (F.card : ℝ) ≤ R.card := by exact_mod_cast hFR
  have hq : ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 ≤ (21 / 2) ^ 4 * (345 * (n : ℝ)) := by
    calc _ ≤ ∑ s ∈ F, (21 / 2) ^ 4 * C s ^ 4 := Finset.sum_le_sum hterm
      _ = (21 / 2) ^ 4 * ∑ s ∈ F, C s ^ 4 := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  rw [← hWF] at hH
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hW4 : (44 / 100 * (n : ℝ)) ^ 4 ≤ (∑ s ∈ Ioc n0 n, (r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hW 4
  have hq0 : 0 ≤ ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have key : (44 / 100 * (n : ℝ)) ^ 4 ≤ (R.card : ℝ) ^ 3 * ((21 / 2) ^ 4 * (345 * (n : ℝ))) := by
    calc _ ≤ _ := hW4
      _ ≤ _ := hH
      _ ≤ (R.card : ℝ) ^ 3 * ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hFR' 3) hq0
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  by_contra hcon
  push Not at hcon
  have hc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have h3 : (R.card : ℝ) ^ 3 ≤ ((n : ℝ) / 600) ^ 3 := pow_le_pow_left₀ hc0 hcon.le 3
  have h4 : (R.card : ℝ) ^ 3 * ((21 / 2) ^ 4 * (345 * (n : ℝ)))
      ≤ ((n : ℝ) / 600) ^ 3 * ((21 / 2) ^ 4 * (345 * (n : ℝ))) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : ((n : ℝ) / 600) ^ 3 * ((21 / 2) ^ 4 * (345 * (n : ℝ))) < (44 / 100 * (n : ℝ)) ^ 4 := by
    have hn4 : 0 < (n : ℝ) ^ 4 := by positivity
    have e1 : ((n : ℝ) / 600) ^ 3 * ((21 / 2) ^ 4 * (345 * (n : ℝ)))
        = (21 / 2) ^ 4 * 345 / 600 ^ 3 * (n : ℝ) ^ 4 := by ring
    have e2 : (44 / 100 * (n : ℝ)) ^ 4 = (44 / 100) ^ 4 * (n : ℝ) ^ 4 := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_right (by norm_num) hn4
  linarith

-- ===== part d =====

theorem s6d_zero_mem_B : 0 ∈ B := ⟨3, Nat.prime_three, by norm_num, rfl⟩

theorem s6d_B_sub_A : B ⊆ A := by
  intro b hb
  open Pointwise in exact Set.mem_add.2 ⟨0, s6d_zero_mem_B, b, hb, zero_add b⟩

theorem s6d_one_mem_A : 1 ∈ A :=
  s6d_B_sub_A ⟨5, by norm_num, by norm_num, rfl⟩

theorem s6d_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

open Classical in
/-- Medium range: `#(A ∩ [1,N]) + 2 ≥ π(2N+3)`. -/
theorem s6d_medium (N : ℕ) :
    Nat.primeCounting (2 * N + 3) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
  set T := (range (2 * N + 4)).filter (fun p => p.Prime ∧ 5 ≤ p) with hT
  have h1 : Nat.primeCounting (2 * N + 3) ≤ #T + 2 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (2 * N + 3 + 1)).filter Nat.Prime ⊆ insert 2 (insert 3 T) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_insert, hT, mem_filter, mem_range]
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨by omega, hp.2, h5⟩)
      · have := hp.2.two_le
        interval_cases p
        · simp
        · simp
        · exact absurd hp.2 (by norm_num)
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans ?_
    have := card_insert_le 3 T
    omega
  have h2 : #T ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
    have hinj : Set.InjOn (fun p => (p - 3) / 2) (T : Set ℕ) := by
      intro p hp q hq hpq
      simp only [hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hp hq
      have := s6d_odd_of_prime hp.2.1 (by omega)
      have := s6d_odd_of_prime hq.2.1 (by omega)
      simp only at hpq
      omega
    rw [← card_image_of_injOn hinj]
    apply card_le_card
    intro a ha
    simp only [hT, mem_image, mem_filter, mem_range] at ha
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩ := ha
    have := s6d_odd_of_prime hp2 (by omega)
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, s6d_B_sub_A ⟨p, hp2, by omega, rfl⟩⟩
  omega

open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem s6d_large (N : ℕ) :
    #((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by
  set T := (range (2 * N + 6 + 1)).filter (fun s => 0 < r s) with hT
  have hmem : ∀ s ∈ T, ∃ p q, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ s = p + q ∧ s ≤ 2 * N + 6 := by
    intro s hs
    simp only [hT, mem_filter, mem_range] at hs
    obtain ⟨hs1, hs2⟩ := hs
    unfold r at hs2
    obtain ⟨p, hp⟩ := card_pos.1 hs2
    simp only [mem_filter, mem_range] at hp
    exact ⟨p, s - p, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by omega, by omega⟩
  have hinj : Set.InjOn (fun s => (s - 6) / 2) (T : Set ℕ) := by
    intro s hs t ht hst
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, -⟩ := hmem s hs
    obtain ⟨p', q', hp', hp2', hq', hq2', rfl, -⟩ := hmem t ht
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := s6d_odd_of_prime hp' hp2'
    have := s6d_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := hp.two_le; have := hq.two_le
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h0 : (p + q - 6) / 2 = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      have : (p + q - 6) / 2 = (p - 3) / 2 + (q - 3) / 2 := by omega
      rw [this]
      open Pointwise in
      exact Set.mem_add.2 ⟨(p - 3) / 2, ⟨p, hp, hp2, rfl⟩, (q - 3) / 2, ⟨q, hq, hq2, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem s6d_two_mem_A : 2 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 1, ⟨5, by norm_num, by norm_num, rfl⟩, rfl⟩

theorem s6d_three_mem_A : 3 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩


theorem n9_mem_B (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : (p - 3) / 2 ∈ B := ⟨p, hp, h2, rfl⟩

theorem n9_small_mem_A (a : ℕ) (h1 : 1 ≤ a) (h10 : a ≤ 10) : a ∈ A := by
  have b0 : 0 ∈ B := n9_mem_B 3 (by norm_num) (by norm_num)
  have b1 : 1 ∈ B := n9_mem_B 5 (by norm_num) (by norm_num)
  have b2 : 2 ∈ B := n9_mem_B 7 (by norm_num) (by norm_num)
  have b4 : 4 ∈ B := n9_mem_B 11 (by norm_num) (by norm_num)
  have b5 : 5 ∈ B := n9_mem_B 13 (by norm_num) (by norm_num)
  open Pointwise in
  interval_cases a
  · exact Set.mem_add.2 ⟨0, b0, 1, b1, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 2, b2, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨0, b0, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨1, b1, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨2, b2, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 4, b4, rfl⟩
  · exact Set.mem_add.2 ⟨4, b4, 5, b5, rfl⟩
  · exact Set.mem_add.2 ⟨5, b5, 5, b5, rfl⟩

open Classical in
/-- `σ(A) ≥ 1/486`. -/
theorem n9_density_A : (1 : ℝ) / 486 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 4860
  · by_cases h10 : 10 ≤ N
    · have h1 : Icc 1 10 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, n9_small_mem_A a ha.1 ha.2⟩
      have h2 := card_le_card h1
      have h3' : (10 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 4860 := by exact_mod_cast hsmall
      linarith
    · have h1 : Icc 1 N ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, ha.2⟩, n9_small_mem_A a ha.1 (by omega)⟩
      have h2 := card_le_card h1
      have h3' : (N : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        rw [Nat.card_Icc] at h2; exact_mod_cast (show N ≤ _ by omega)
      linarith
  push Not at hsmall
  have hN' : (4861 : ℝ) ≤ N := by exact_mod_cast hsmall
  by_cases hbig : Real.exp 550 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := n9_R _ hbig
    have hL := s6d_large N
    have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
        ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
    push_cast at hR hbig
    nlinarith
  · push Not at hbig
    have hy : (1000 : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hP := pi_lower _ hy
    rw [Nat.floor_natCast] at hP
    have hM := s6d_medium N
    have hM' : (Nat.primeCounting (2 * N + 3) : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
      exact_mod_cast hM
    have hypos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by linarith
    have hlog : Real.log ((2 * N + 3 : ℕ) : ℝ) < 550 := by
      rw [Real.log_lt_iff_lt_exp hypos]
      push_cast at hbig ⊢; linarith
    have hlogpos : 0 < Real.log ((2 * N + 3 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hfrac : 2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * 550) ≤
        2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * Real.log ((2 * N + 3 : ℕ) : ℝ)) := by
      gcongr
    push_cast at hfrac hP
    nlinarith

open Pointwise

theorem s6m_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def s6m_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem s6m_P_add {j k t u : ℕ} (h1 : s6m_P j t) (h2 : s6m_P k u) : s6m_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem s6m_P_B {b : ℕ} (hb : b ∈ B) : s6m_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem s6m_P_A {a : ℕ} (ha : a ∈ A) : s6m_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact s6m_P_add (s6m_P_B hb) (s6m_P_B hc)


theorem n9_P_multiset (t : Multiset ℕ) (ht : ∀ x ∈ t, x ∈ A) : s6m_P (2 * t.card) t.sum := by
  induction t using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | cons a t ih =>
    have h1 := ih (fun x hx => ht x (Multiset.mem_cons_of_mem hx))
    have h2 := s6m_P_A (ht a (Multiset.mem_cons_self a t))
    have := s6m_P_add h2 h1
    rw [Multiset.card_cons, Multiset.sum_cons]
    rwa [show 2 * (t.card + 1) = 2 + 2 * t.card by ring]

open Classical in
theorem n9_all (t : ℕ) : s6m_P 972 t := by
  have hA := n9_density_A
  have hk : (1 : ℝ) ≤ ((486 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 486 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd `n ≥ 1947` is a sum of exactly `973` primes. -/
theorem exact_973 (n : ℕ) (hodd : Odd n) (hn : 1947 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 973 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 2919 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all ((n - 2919) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 1946) 3 + Multiset.replicate (2919 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end Schnir

/-- The campaign goal (platform theorem `odd_sum_le_973_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 973 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 1947 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := Schnir.exact_973 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega
