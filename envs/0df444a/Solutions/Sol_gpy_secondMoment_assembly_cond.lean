-- Prove2me | solution 1 for gpy_secondMoment_assembly_cond
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T21:29:08.977948+00:00
-- url     : https://prove2.me/submissions/7447543b-6a87-4f6a-aabf-d2978140c5f0

/-
  Submission file for the Prove2Me problem `gpy_secondMoment_assembly_cond`
  (publish2 batch, conditional GPY assembly).

  Self-contained: imports Mathlib only. Contains the verified
  bodies of the dependency chain (weights, count, main term,
  second moment, BV, BV error control, BV instantiation,
  weighted BV, Selberg weight, tau moments, fiber bound,
  divisor-weighted BV, Euler product, monomial evaluation,
  conditional monomial evaluation, assembly) plus the restated
  theorem, with top-level `theorem solution` in the problem's
  exact binder/statement form (statement mechanically extracted
  from the restated theorem, so the two are textually identical
  modulo the name). No sorry tactic, no axioms beyond the
  standard ones, no platform imports. The conditional theorem
  is published AS a conditional theorem (hMono and hDiv as
  explicit hypotheses).
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY


/-- The support set for tuple Selberg weights at level R: tuples of positive
    integers, each at most R, whose product is at most R. -/
def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

/-- Membership in the support set, unfolded. -/
theorem mem_tupleSupport {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

/-- The GPY weight at n for the tuple h, level R, and coefficients λ:
    the square of the divisor sum over the support. -/
noncomputable def weight (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ tupleSupport k R, if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2

/-- Weights are squares, hence nonnegative. -/
theorem weight_nonneg (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) :
    0 ≤ weight k h R lam n := by
  unfold weight
  exact sq_nonneg _

/-- Diagonal expansion of the weight: the square of the sum is the double
    sum of pairwise products. This is the tuple analogue of the platform's
    λ² diagonalization. -/
theorem weight_expand (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) :
    weight k h R lam n =
      ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if (∀ i, d i ∣ n + h i) then lam d else 0) *
          (if (∀ i, e i ∣ n + h i) then lam e else 0) := by
  unfold weight
  rw [pow_two, Finset.sum_mul_sum]

/-- Size bound: the weight is at most the square of the ℓ¹ mass of λ. -/
theorem weight_le (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) :
    weight k h R lam n ≤ (∑ d ∈ tupleSupport k R, |lam d|) ^ 2 := by
  have h1 : |∑ d ∈ tupleSupport k R,
        (if (∀ i, d i ∣ n + h i) then lam d else 0)|
      ≤ ∑ d ∈ tupleSupport k R, |lam d| := by
    calc |∑ d ∈ tupleSupport k R,
          (if (∀ i, d i ∣ n + h i) then lam d else 0)|
        ≤ ∑ d ∈ tupleSupport k R,
          |(if (∀ i, d i ∣ n + h i) then lam d else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ tupleSupport k R, |lam d| :=
        Finset.sum_le_sum (fun d _ => by
          by_cases hd : (∀ i, d i ∣ n + h i) <;> simp [hd])
  unfold weight
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- First-moment interchange: the sum of the weights over an interval equals
    the diagonal double sum of λ_d λ_e times the joint-divisibility count.
    This is the first-moment main-term structure; the arithmetic estimate of
    the count itself is the next pass. -/
theorem firstMoment_eq (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) :
    ∑ n ∈ Finset.Ioc x y, weight k h R lam n =
      ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        lam d * lam e *
          ((Finset.filter
            (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
            (Finset.Ioc x y)).card : ℝ) := by
  have inner : ∀ d e : Fin k → ℕ,
      ∑ n ∈ Finset.Ioc x y,
          (if (∀ i, d i ∣ n + h i) then lam d else 0) *
            (if (∀ i, e i ∣ n + h i) then lam e else 0)
        = lam d * lam e *
          ((Finset.filter
            (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
            (Finset.Ioc x y)).card : ℝ) := by
    intro d e
    have h1 : ∀ n : ℕ,
        (if (∀ i, d i ∣ n + h i) then lam d else 0) *
          (if (∀ i, e i ∣ n + h i) then lam e else 0)
        = if (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i
          then lam d * lam e else 0 := by
      intro n
      by_cases hd : (∀ i, d i ∣ n + h i) <;>
        by_cases he : (∀ i, e i ∣ n + h i) <;> simp [hd, he]
    rw [Finset.sum_congr rfl (fun n _ => h1 n)]
    have h2 : ∀ n : ℕ,
        (if (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i
          then lam d * lam e else 0)
        = lam d * lam e *
          (if (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i
            then (1 : ℝ) else 0) := by
      intro n
      by_cases hc : (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i <;> simp [hc]
    rw [Finset.sum_congr rfl (fun n _ => h2 n), ← Finset.mul_sum,
      Finset.sum_boole]
  calc ∑ n ∈ Finset.Ioc x y, weight k h R lam n
      = ∑ n ∈ Finset.Ioc x y, ∑ d ∈ tupleSupport k R,
          ∑ e ∈ tupleSupport k R,
            (if (∀ i, d i ∣ n + h i) then lam d else 0) *
              (if (∀ i, e i ∣ n + h i) then lam e else 0) :=
        Finset.sum_congr rfl (fun n _ => weight_expand k h R lam n)
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          ∑ n ∈ Finset.Ioc x y,
            (if (∀ i, d i ∣ n + h i) then lam d else 0) *
              (if (∀ i, e i ∣ n + h i) then lam e else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          lam d * lam e *
            ((Finset.filter
              (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
              (Finset.Ioc x y)).card : ℝ) :=
        Finset.sum_congr rfl (fun d _ =>
          Finset.sum_congr rfl (fun e _ => inner d e))


/-- CRT existence: for pairwise-coprime moduli, the system `m i ∣ n + h i`
    has a particular solution. The residues are `m i - h i % m i`, chosen so
    that each residue plus `h i` is divisible by `m i`. -/
theorem exists_crt_solution {k : ℕ} {m h : Fin k → ℕ}
    (hcop : Set.Pairwise (Finset.univ : Finset (Fin k)) (Nat.Coprime on m))
    (hm : ∀ i, m i ≠ 0) :
    ∃ a : ℕ, ∀ i, m i ∣ a + h i := by
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (a := fun i => m i - h i % m i) (s := m)
    Finset.univ (fun i _ => hm i) hcop
  refine ⟨a, fun i => ?_⟩
  have hi : a ≡ m i - h i % m i [MOD m i] := ha i (Finset.mem_univ i)
  have hmod : a + h i ≡ (m i - h i % m i) + h i [MOD m i] := hi.add_right (h i)
  have hzero : (m i - h i % m i) + h i ≡ 0 [MOD m i] := by
    rw [Nat.modEq_zero_iff_dvd]
    have h3 : (m i - h i % m i) + h i = m i * (h i / m i + 1) := by
      have h1 := Nat.div_add_mod (h i) (m i)
      have h2 : h i % m i ≤ m i :=
        (Nat.mod_lt (h i) (Nat.pos_of_ne_zero (hm i))).le
      calc (m i - h i % m i) + h i
          = (m i - h i % m i) + (m i * (h i / m i) + h i % m i) := by rw [h1]
        _ = m i * (h i / m i) + m i := by
            rw [Nat.add_comm (m i - h i % m i) (m i * (h i / m i) + h i % m i),
              Nat.add_assoc, Nat.add_sub_cancel' h2]
        _ = m i * (h i / m i + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
    rw [h3]
    exact dvd_mul_right _ _
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans hzero)

/-- CRT reduction: under pairwise coprimality, the joint-divisibility system
    is equivalent to a single residue class modulo the product of the moduli. -/
theorem jointDivisibility_iff_modEq {k : ℕ} {m h : Fin k → ℕ}
    (hcop : Set.Pairwise (Finset.univ : Finset (Fin k)) (Nat.Coprime on m))
    (_hm : ∀ i, m i ≠ 0) (a : ℕ) (ha : ∀ i, m i ∣ a + h i) (n : ℕ) :
    (∀ i, m i ∣ n + h i) ↔ n ≡ a [MOD ∏ i, m i] := by
  constructor
  · intro hn
    have hmod : ∀ i, n ≡ a [MOD m i] := fun i => by
      have h1 : n + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (hn i)
      have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
      exact Nat.ModEq.add_right_cancel' (h i) (h1.trans h2.symm)
    have hpair : (List.finRange k).Pairwise (Nat.Coprime on m) :=
      List.Nodup.pairwise_of_forall_ne (List.nodup_finRange k)
        (fun i _ j _ hij => hcop (Finset.mem_coe.mpr (Finset.mem_univ i))
          (Finset.mem_coe.mpr (Finset.mem_univ j)) hij)
    rw [Fin.prod_univ_def]
    exact (Nat.modEq_list_map_prod_iff hpair).mpr (fun i _ => hmod i)
  · intro hn i
    have hmi : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hmod : n ≡ a [MOD m i] := Nat.ModEq.of_dvd hmi hn
    have h1 : n + h i ≡ a + h i [MOD m i] := hmod.add_right (h i)
    have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)

/-- The two-tuple divisibility condition in `firstMoment_eq` is the same as
    the single-modulus condition with coordinatewise lcms. -/
theorem filter_jointDivisibility_eq {k : ℕ} {d e h : Fin k → ℕ} (x y : ℕ) :
    (Finset.filter
        (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
        (Finset.Ioc x y))
      = Finset.filter
        (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ n + h i)
        (Finset.Ioc x y) := by
  apply Finset.filter_congr
  intro n _
  constructor
  · rintro ⟨hd, he⟩ i
    exact Nat.lcm_dvd (hd i) (he i)
  · intro h
    exact ⟨fun i => (dvd_lcm_left _ _).trans (h i),
      fun i => (dvd_lcm_right _ _).trans (h i)⟩

/-- The interval count bound: for pairwise-coprime moduli, the number of
    `n ∈ Ioc x y` satisfying all the divisibilities is `(y - x) / L` up to
    an error of at most 1, where `L` is the product of the moduli. -/
theorem count_jointDivisibility {k : ℕ} {m h : Fin k → ℕ}
    (hcop : Set.Pairwise (Finset.univ : Finset (Fin k)) (Nat.Coprime on m))
    (hm : ∀ i, m i ≠ 0) {x y : ℕ} (hxy : x ≤ y) :
    abs ( ((Finset.filter (fun n => ∀ i, m i ∣ n + h i) (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) / (∏ i, m i) ) ≤ 1 := by
  classical
  have hLpos : 0 < ∏ i, m i :=
    Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (hm i))
  obtain ⟨a, ha⟩ := exists_crt_solution hcop hm
  have hset : (Finset.filter (fun n => ∀ i, m i ∣ n + h i) (Finset.Ioc x y))
      = Finset.filter (fun n => n ≡ a [MOD ∏ i, m i]) (Finset.Ioc x y) := by
    apply Finset.filter_congr
    intro n _
    exact jointDivisibility_iff_modEq hcop hm a ha n
  rw [hset]
  have hcardZ : ((Finset.filter (fun n => n ≡ a [MOD ∏ i, m i])
      (Finset.Ioc x y)).card : ℤ)
      = max (⌊((y : ℚ) - a) / (∏ i, m i)⌋ - ⌊((x : ℚ) - a) / (∏ i, m i)⌋) 0 :=
    Nat.Ioc_filter_modEq_card x y hLpos a
  have hL' : (0 : ℚ) < (∏ i, m i) := by exact_mod_cast hLpos
  have hle : ((x : ℚ) - a) / (∏ i, m i) ≤ ((y : ℚ) - a) / (∏ i, m i) := by
    rw [div_le_div_iff_of_pos_right hL']
    exact sub_le_sub_right (by exact_mod_cast hxy) _
  have hF : ⌊((x : ℚ) - a) / (∏ i, m i)⌋ ≤ ⌊((y : ℚ) - a) / (∏ i, m i)⌋ := by
    have h1 := Int.floor_le (((x : ℚ) - a) / (∏ i, m i))
    have h2 := Int.lt_floor_add_one (((y : ℚ) - a) / (∏ i, m i))
    have h3 : (⌊((x : ℚ) - a) / (∏ i, m i)⌋ : ℚ)
        < ⌊((y : ℚ) - a) / (∏ i, m i)⌋ + 1 :=
      lt_of_le_of_lt (le_trans h1 hle) h2
    have h4 : ⌊((x : ℚ) - a) / (∏ i, m i)⌋
        < ⌊((y : ℚ) - a) / (∏ i, m i)⌋ + 1 := by
      exact_mod_cast h3
    exact Int.lt_add_one_iff.mp h4
  rw [max_eq_left (sub_nonneg.mpr hF)] at hcardZ
  have hQ : abs (((Finset.filter (fun n => n ≡ a [MOD ∏ i, m i])
      (Finset.Ioc x y)).card : ℚ)
      - ((y : ℚ) - x) / (∏ i, m i)) ≤ 1 := by
    have hcardQ : ((Finset.filter (fun n => n ≡ a [MOD ∏ i, m i])
        (Finset.Ioc x y)).card : ℚ)
        = (⌊((y : ℚ) - a) / (∏ i, m i)⌋ : ℚ)
          - (⌊((x : ℚ) - a) / (∏ i, m i)⌋ : ℚ) := by
      exact_mod_cast hcardZ
    rw [hcardQ, abs_le]
    have hb1 := Int.floor_le (((y : ℚ) - a) / (∏ i, m i))
    have hb2 := Int.lt_floor_add_one (((y : ℚ) - a) / (∏ i, m i))
    have hb3 := Int.floor_le (((x : ℚ) - a) / (∏ i, m i))
    have hb4 := Int.lt_floor_add_one (((x : ℚ) - a) / (∏ i, m i))
    have hpq : ((y : ℚ) - a) / (∏ i, m i) - ((x : ℚ) - a) / (∏ i, m i)
        = ((y : ℚ) - x) / (∏ i, m i) := by
      rw [← sub_div]
      congr 1
      ring
    constructor <;> linarith
  have h2 : (abs (((Finset.filter (fun n => n ≡ a [MOD ∏ i, m i])
      (Finset.Ioc x y)).card : ℚ)
      - ((y : ℚ) - x) / (∏ i, m i)) : ℝ) ≤ 1 := by
    exact_mod_cast hQ
  push_cast at h2 ⊢
  exact h2

/-- The count bound in the exact form `firstMoment_eq` needs: two tuples,
    coordinatewise lcms as moduli. -/
theorem count_jointDivisibility_lcm {k : ℕ} {d e h : Fin k → ℕ}
    (hcop : Set.Pairwise (Finset.univ : Finset (Fin k))
      (Nat.Coprime on fun i => Nat.lcm (d i) (e i)))
    (hm : ∀ i, Nat.lcm (d i) (e i) ≠ 0) {x y : ℕ} (hxy : x ≤ y) :
    abs ( ((Finset.filter
        (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
        (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) / (∏ i, Nat.lcm (d i) (e i)) ) ≤ 1 := by
  rw [filter_jointDivisibility_eq]
  exact count_jointDivisibility hcop hm hxy


/-! ### Binary gcd/lcm distributivity -/

/-- `gcd (lcm a b) c = lcm (gcd a c) (gcd b c)`, by prime factorization. -/
theorem gcd_lcm_distrib {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  have hlab : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hgac : Nat.gcd a c ≠ 0 := by
    intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  have hgbc : Nat.gcd b c ≠ 0 := by
    intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  refine Nat.eq_of_factorization_eq ?_ ?_ ?_
  · intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  · exact Nat.lcm_ne_zero hgac hgbc
  · intro p
    rw [Nat.factorization_gcd hlab hc, Nat.factorization_lcm ha hb,
        Nat.factorization_lcm hgac hgbc, Nat.factorization_gcd ha hc,
        Nat.factorization_gcd hb hc]
    simp only [Finsupp.inf_apply, Finsupp.sup_apply]
    omega

/-! ### Finset versions: gcd distributes over `Finset.lcm`, and ModEq lifts to it -/

/-- `gcd` distributes over a `Finset.lcm` (by induction, using the binary case). -/
theorem gcd_finset_lcm {k : ℕ} (s : Finset (Fin k)) {m : Fin k → ℕ} {n : ℕ} :
    (∀ i ∈ s, m i ≠ 0) → n ≠ 0 →
    Nat.gcd (s.lcm m) n = s.lcm (fun i => Nat.gcd (m i) n) := by
  induction s using Finset.induction with
  | empty =>
    intro _ _
    rw [Finset.lcm_empty, Finset.lcm_empty, Nat.gcd_one_left]
  | @insert j s hj ih =>
    intro hm' hn'
    have hm_s : ∀ i ∈ s, m i ≠ 0 := fun i hi => hm' i (Finset.mem_insert_of_mem hi)
    have hj_ne : m j ≠ 0 := hm' j (Finset.mem_insert_self j s)
    have hLs_ne : s.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr hm_s
    calc Nat.gcd ((insert j s).lcm m) n
        = Nat.gcd (Nat.lcm (m j) (s.lcm m)) n := by
          rw [Finset.lcm_insert, lcm_eq_nat_lcm]
      _ = Nat.lcm (Nat.gcd (m j) n) (Nat.gcd (s.lcm m) n) :=
          gcd_lcm_distrib hj_ne hLs_ne hn'
      _ = Nat.lcm (Nat.gcd (m j) n) (s.lcm (fun i => Nat.gcd (m i) n)) := by
          rw [ih hm_s hn']
      _ = (insert j s).lcm (fun i => Nat.gcd (m i) n) := by
          rw [Finset.lcm_insert, lcm_eq_nat_lcm]

/-- Simultaneous congruences mod each `m i` combine to a congruence mod `s.lcm m`. -/
theorem modEq_finset_lcm {k : ℕ} (s : Finset (Fin k)) {m : Fin k → ℕ} {a b : ℕ} :
    (∀ i ∈ s, a ≡ b [MOD m i]) → a ≡ b [MOD s.lcm m] := by
  induction s using Finset.induction with
  | empty =>
    intro _
    rw [Finset.lcm_empty]
    exact Nat.modEq_one
  | @insert j s hj ih =>
    intro h'
    have h1 : a ≡ b [MOD m j] := h' j (Finset.mem_insert_self j s)
    have h2 : a ≡ b [MOD s.lcm m] :=
      ih (fun i hi => h' i (Finset.mem_insert_of_mem hi))
    rw [Finset.lcm_insert, lcm_eq_nat_lcm]
    exact Nat.mod_lcm h1 h2

/-! ### General (non-coprime) Chinese remainder theorem -/

/-- General CRT, residue form: compatible residues have a simultaneous solution.
    The two-modulus step is `Nat.chineseRemainder'`; the transfer of the
    induction hypothesis to the combined modulus uses `gcd_finset_lcm`
    and `modEq_finset_lcm`. -/
theorem exists_modEq_of_compatible {k : ℕ} {m r : Fin k → ℕ} :
    (∀ i, m i ≠ 0) → (∀ i j, r i ≡ r j [MOD Nat.gcd (m i) (m j)]) →
    ∃ a, ∀ i, a ≡ r i [MOD m i] := by
  intro hm hcompat
  have key : ∀ s : Finset (Fin k), (∀ i ∈ s, m i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD Nat.gcd (m i) (m j)]) →
      ∃ a, ∀ i ∈ s, a ≡ r i [MOD m i] := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro _ _
      exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | @insert j s hj ih =>
      intro hm' hcompat'
      have hm_s : ∀ i ∈ s, m i ≠ 0 := fun i hi => hm' i (Finset.mem_insert_of_mem hi)
      have hcompat_s : ∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD Nat.gcd (m i) (m j)] :=
        fun i hi j hj' => hcompat' i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj')
      obtain ⟨a, ha⟩ := ih hm_s hcompat_s
      have htransfer : a ≡ r j [MOD Nat.gcd (s.lcm m) (m j)] := by
        have h1 : ∀ i ∈ s, a ≡ r j [MOD Nat.gcd (m i) (m j)] := by
          intro i hi
          have hai : a ≡ r i [MOD m i] := ha i hi
          have h2 : a ≡ r i [MOD Nat.gcd (m i) (m j)] :=
            Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _) hai
          have h3 : r i ≡ r j [MOD Nat.gcd (m i) (m j)] :=
            hcompat' i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j s)
          exact h2.trans h3
        have h2 := modEq_finset_lcm s (m := fun i => Nat.gcd (m i) (m j)) h1
        rw [← gcd_finset_lcm s hm_s (hm' j (Finset.mem_insert_self j s))] at h2
        exact h2
      obtain ⟨b, hb⟩ := Nat.chineseRemainder' htransfer
      refine ⟨b, fun i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hb.2
      · have h1 : b ≡ a [MOD m i] := Nat.ModEq.of_dvd (Finset.dvd_lcm hi) hb.1
        exact h1.trans (ha i hi)
  obtain ⟨a, ha⟩ := key Finset.univ (fun i _ => hm i) (fun i _ j _ => hcompat i j)
  exact ⟨a, fun i => ha i (Finset.mem_univ i)⟩

/-- General CRT, divisibility form: a compatible family of shifts has a common
    `a` with every `m i ∣ a + h i`. Residues are `m i - h i % m i`. -/
theorem exists_dvd_of_compatible {k : ℕ} {m h : Fin k → ℕ} :
    (∀ i, m i ≠ 0) → (∀ i j, h i ≡ h j [MOD Nat.gcd (m i) (m j)]) →
    ∃ a, ∀ i, m i ∣ a + h i := by
  intro hm hcompat
  have hri : ∀ i, m i ∣ (m i - h i % m i) + h i := by
    intro i
    have h3 : (m i - h i % m i) + h i = m i * (h i / m i + 1) := by
      have h1 := Nat.div_add_mod (h i) (m i)
      have h2 : h i % m i ≤ m i := (Nat.mod_lt (h i) (Nat.pos_of_ne_zero (hm i))).le
      calc (m i - h i % m i) + h i
          = (m i - h i % m i) + (m i * (h i / m i) + h i % m i) := by rw [h1]
        _ = m i * (h i / m i) + m i := by
            rw [Nat.add_comm (m i - h i % m i) (m i * (h i / m i) + h i % m i),
              Nat.add_assoc, Nat.add_sub_cancel' h2]
        _ = m i * (h i / m i + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [h3]
    exact dvd_mul_right _ _
  have hcompat_r : ∀ i j, (m i - h i % m i) ≡ (m j - h j % m j)
      [MOD Nat.gcd (m i) (m j)] := by
    intro i j
    have g1 : (m i - h i % m i) + h i ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _)
        (Nat.modEq_zero_iff_dvd.mpr (hri i))
    have g2 : (m j - h j % m j) + h j ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_right _ _)
        (Nat.modEq_zero_iff_dvd.mpr (hri j))
    have h3 : (m i - h i % m i) + h i ≡ (m j - h j % m j) + h j
        [MOD Nat.gcd (m i) (m j)] :=
      g1.trans g2.symm
    have h4 : (m j - h j % m j) + h j ≡ (m j - h j % m j) + h i
        [MOD Nat.gcd (m i) (m j)] := by
      rw [Nat.gcd_comm (m i) (m j)]
      exact (hcompat j i).add_left _
    exact Nat.ModEq.add_right_cancel' (h i) (h3.trans h4)
  obtain ⟨a, ha⟩ := exists_modEq_of_compatible hm hcompat_r
  refine ⟨a, fun i => ?_⟩
  have h1 : a + h i ≡ (m i - h i % m i) + h i [MOD m i] := (ha i).add_right (h i)
  have h2 : (m i - h i % m i) + h i ≡ 0 [MOD m i] :=
    Nat.modEq_zero_iff_dvd.mpr (hri i)
  exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)

/-! ### The floor argument, factored out over an abstract modulus -/

/-- Count of one residue class mod `L` in an interval, to within 1.
    This is the floor argument from `GPYCount.count_jointDivisibility`,
    factored out so it can be reused with `L = Finset.lcm univ m`. -/
theorem abs_card_Ioc_filter_modEq_sub (L a x y : ℕ) (hL : 0 < L) (hxy : x ≤ y) :
    abs (((Finset.filter (fun n => n ≡ a [MOD L]) (Finset.Ioc x y)).card : ℝ)
      - ((y : ℝ) - x) / (L : ℝ)) ≤ 1 := by
  have hcardZ : ((Finset.filter (fun n => n ≡ a [MOD L])
      (Finset.Ioc x y)).card : ℤ)
      = max (⌊((y : ℚ) - a) / (L : ℚ)⌋ - ⌊((x : ℚ) - a) / (L : ℚ)⌋) 0 :=
    Nat.Ioc_filter_modEq_card x y hL a
  have hL' : (0 : ℚ) < (L : ℚ) := by exact_mod_cast hL
  have hle : ((x : ℚ) - a) / (L : ℚ) ≤ ((y : ℚ) - a) / (L : ℚ) := by
    rw [div_le_div_iff_of_pos_right hL']
    exact sub_le_sub_right (by exact_mod_cast hxy) _
  have hF : ⌊((x : ℚ) - a) / (L : ℚ)⌋ ≤ ⌊((y : ℚ) - a) / (L : ℚ)⌋ := by
    have h1 := Int.floor_le (((x : ℚ) - a) / (L : ℚ))
    have h2 := Int.lt_floor_add_one (((y : ℚ) - a) / (L : ℚ))
    have h3 : (⌊((x : ℚ) - a) / (L : ℚ)⌋ : ℚ)
        < ⌊((y : ℚ) - a) / (L : ℚ)⌋ + 1 :=
      lt_of_le_of_lt (le_trans h1 hle) h2
    have h4 : ⌊((x : ℚ) - a) / (L : ℚ)⌋
        < ⌊((y : ℚ) - a) / (L : ℚ)⌋ + 1 := by
      exact_mod_cast h3
    exact Int.lt_add_one_iff.mp h4
  rw [max_eq_left (sub_nonneg.mpr hF)] at hcardZ
  have hQ : abs (((Finset.filter (fun n => n ≡ a [MOD L])
      (Finset.Ioc x y)).card : ℚ)
      - ((y : ℚ) - x) / (L : ℚ)) ≤ 1 := by
    have hcardQ : ((Finset.filter (fun n => n ≡ a [MOD L])
        (Finset.Ioc x y)).card : ℚ)
        = (⌊((y : ℚ) - a) / (L : ℚ)⌋ : ℚ)
          - (⌊((x : ℚ) - a) / (L : ℚ)⌋ : ℚ) := by
      exact_mod_cast hcardZ
    rw [hcardQ, abs_le]
    have hb1 := Int.floor_le (((y : ℚ) - a) / (L : ℚ))
    have hb2 := Int.lt_floor_add_one (((y : ℚ) - a) / (L : ℚ))
    have hb3 := Int.floor_le (((x : ℚ) - a) / (L : ℚ))
    have hb4 := Int.lt_floor_add_one (((x : ℚ) - a) / (L : ℚ))
    have hpq : ((y : ℚ) - a) / (L : ℚ) - ((x : ℚ) - a) / (L : ℚ)
        = ((y : ℚ) - x) / (L : ℚ) := by
      rw [← sub_div]
      congr 1
      ring
    constructor <;> linarith
  have h2 : (abs (((Finset.filter (fun n => n ≡ a [MOD L])
      (Finset.Ioc x y)).card : ℚ)
      - ((y : ℚ) - x) / (L : ℚ)) : ℝ) ≤ 1 := by
    exact_mod_cast hQ
  push_cast at h2 ⊢
  exact h2

/-! ### General count: compatible case, and the incompatible case -/

/-- General count bound: under the compatibility hypothesis, the joint
    divisibility count in `(x, y]` is `(y - x) / L` to within 1, where
    `L` is the lcm of all the moduli. -/
theorem count_general {k : ℕ} {m h : Fin k → ℕ} :
    (∀ i, m i ≠ 0) → (∀ i j, h i ≡ h j [MOD Nat.gcd (m i) (m j)]) →
    {x y : ℕ} → x ≤ y →
    abs (((Finset.filter (fun n => ∀ i, m i ∣ n + h i) (Finset.Ioc x y)).card : ℝ)
      - ((y : ℝ) - x) / Finset.lcm Finset.univ m) ≤ 1 := by
  intro hm hcompat x y hxy
  obtain ⟨a, ha⟩ := exists_dvd_of_compatible hm hcompat
  have hset : (Finset.filter (fun n => ∀ i, m i ∣ n + h i) (Finset.Ioc x y))
      = Finset.filter (fun n => n ≡ a [MOD Finset.lcm Finset.univ m])
        (Finset.Ioc x y) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · intro hn
      have hmod : ∀ i, n ≡ a [MOD m i] := fun i => by
        have h1 : n + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (hn i)
        have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
        exact Nat.ModEq.add_right_cancel' (h i) (h1.trans h2.symm)
      exact modEq_finset_lcm Finset.univ (fun i _ => hmod i)
    · intro hn i
      have hmi : m i ∣ Finset.lcm Finset.univ m := Finset.dvd_lcm (Finset.mem_univ i)
      have hmod : n ≡ a [MOD m i] := Nat.ModEq.of_dvd hmi hn
      have h1 : n + h i ≡ a + h i [MOD m i] := hmod.add_right (h i)
      have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
      exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)
  rw [hset]
  have hLpos : 0 < Finset.lcm Finset.univ m :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _ => hm i))
  exact abs_card_Ioc_filter_modEq_sub _ _ _ _ hLpos hxy

/-- Incompatible case: if some pair of shifts is incompatible mod the gcd
    of their moduli, no `n` satisfies all the divisibilities. -/
theorem count_eq_zero_of_incompatible {k : ℕ} {m h : Fin k → ℕ} {x y : ℕ} :
    (∃ i j, ¬ (h i ≡ h j [MOD Nat.gcd (m i) (m j)])) →
    (Finset.filter (fun n => ∀ i, m i ∣ n + h i) (Finset.Ioc x y)).card = 0 := by
  intro hincompat
  rw [Finset.card_eq_zero]
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨-, hn⟩ := h
  obtain ⟨i, j, hij⟩ := hincompat
  have h1 : n + h i ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _)
      (Nat.modEq_zero_iff_dvd.mpr (hn i))
  have h2 : n + h j ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right _ _)
      (Nat.modEq_zero_iff_dvd.mpr (hn j))
  have h3 : h i ≡ h j [MOD Nat.gcd (m i) (m j)] :=
    Nat.ModEq.add_left_cancel' n (h1.trans h2.symm)
  exact hij h3

/-! ### Two-tuple corollaries, in `firstMoment_eq`'s form -/

/-- The general count bound for a pair of support tuples, with moduli
    `Nat.lcm (d i) (e i)` and `L` the lcm over coordinates. -/
theorem count_twoTuple {k : ℕ} {d e h : Fin k → ℕ} :
    (∀ i, Nat.lcm (d i) (e i) ≠ 0) →
    (∀ i j, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) →
    {x y : ℕ} → x ≤ y →
    abs (((Finset.filter (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y)).card : ℝ)
      - ((y : ℝ) - x) / Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i)))
      ≤ 1 := by
  intro hm hcompat x y hxy
  rw [filter_jointDivisibility_eq]
  exact count_general hm hcompat hxy

/-- The incompatible case for a pair of support tuples: the count is 0. -/
theorem count_twoTuple_eq_zero {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ} :
    (∃ i j, ¬ (h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])) →
    (Finset.filter (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y)).card = 0 := by
  intro hincompat
  rw [filter_jointDivisibility_eq]
  exact count_eq_zero_of_incompatible hincompat

/-! ### The first-moment main term -/

/-- First-moment main term for GPY tuple weights (general-compatibility version).

    The first moment `∑_{x < n ≤ y} weight k h R lam n` equals
    `(y - x)` times the sum of `lam d * lam e / L(d, e)` over the
    *compatible* support pairs, up to an error bounded by the sum of
    `|lam d * lam e|` over the compatible pairs. Incompatible pairs
    contribute exactly 0 to both the moment and the main term, so they
    do not appear in the error at all. -/
theorem firstMoment_mainTerm (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y) :
    abs (∑ n ∈ Finset.Ioc x y, weight k h R lam n
      - ((y : ℝ) - x) * ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
              h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
           then lam d * lam e /
             Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
           else 0))
    ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
              h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then abs (lam d * lam e) else 0) := by
  have per_term : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (lam d * lam e * ((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) * (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then lam d * lam e /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
          else 0))
      ≤ (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then abs (lam d * lam e) else 0) := by
    intro d hd e he
    have hd1 : ∀ i, 1 ≤ d i := (mem_tupleSupport.mp hd).1
    have he1 : ∀ i, 1 ≤ e i := (mem_tupleSupport.mp he).1
    have hne : ∀ i, Nat.lcm (d i) (e i) ≠ 0 := fun i => by
      have hdi : 1 ≤ d i := hd1 i
      have hei : 1 ≤ e i := he1 i
      exact Nat.lcm_ne_zero (by omega) (by omega)
    by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
        h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    · rw [if_pos hc, if_pos hc]
      have hbound := count_twoTuple hne
        (fun i j => hc i (Finset.mem_univ i) j (Finset.mem_univ j)) hxy
      have heq : lam d * lam e * ((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
          - ((y : ℝ) - x) * (lam d * lam e /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i)))
          = lam d * lam e * (((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
          - ((y : ℝ) - x) /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))) := by
        ring
      rw [heq, abs_mul]
      calc abs (lam d * lam e) * abs (((Finset.filter
            (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
            (Finset.Ioc x y)).card : ℝ)
            - ((y : ℝ) - x) /
              Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i)))
          ≤ abs (lam d * lam e) * 1 :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
        _ = abs (lam d * lam e) := mul_one _
    · rw [if_neg hc, if_neg hc]
      push_neg at hc
      obtain ⟨i, -, j, -, hij⟩ := hc
      have hzero := count_twoTuple_eq_zero (k := k) (d := d) (e := e) (h := h)
        (x := x) (y := y) ⟨i, j, hij⟩
      rw [hzero, Nat.cast_zero, mul_zero, mul_zero, sub_zero, abs_zero]
  rw [firstMoment_eq]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc abs (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (lam d * lam e * ((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) * (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then lam d * lam e /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
          else 0)))
      ≤ ∑ d ∈ tupleSupport k R, abs (∑ e ∈ tupleSupport k R,
        (lam d * lam e * ((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) * (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then lam d * lam e /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
          else 0))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e * ((Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y)).card : ℝ)
        - ((y : ℝ) - x) * (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then lam d * lam e /
            Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
          else 0)) :=
        Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
          then abs (lam d * lam e) else 0) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => per_term d hd e he))


/-- The prime indicator: 1 if `m` is prime, 0 otherwise, as a real number. -/
def primeInd (m : ℕ) : ℝ := if Nat.Prime m then 1 else 0

/-- The linear GPY second moment: the prime sum over the tuple, weighted by
    the tuple weight, summed over the interval. -/
noncomputable def secondMoment (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x y, (∑ i, primeInd (n + h i)) * weight k h R lam n

/-- The squared variant of the second moment (supporting lemma only): the
    square of the prime sum, weighted, summed over the interval. -/
noncomputable def secondMomentSq (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x y, (∑ i, primeInd (n + h i)) ^ 2 * weight k h R lam n

/-- The prime indicator is idempotent: its square is itself. -/
theorem primeInd_sq (m : ℕ) : primeInd m * primeInd m = primeInd m := by
  unfold primeInd
  by_cases hp : Nat.Prime m <;> simp [hp]

/-- The product of two prime indicators is the indicator of the conjunction. -/
theorem primeInd_mul (a b : ℕ) :
    primeInd a * primeInd b =
      if (Nat.Prime a ∧ Nat.Prime b) then (1 : ℝ) else 0 := by
  unfold primeInd
  by_cases ha : Nat.Prime a <;> by_cases hb : Nat.Prime b <;> simp [ha, hb]

/-- General interchange: weighting any function `g` by the tuple weight and
    summing over an interval diagonalizes into the joint-divisibility sums
    of `g`. This follows the proof pattern of `firstMoment_eq`. -/
theorem weightedSum_interchange (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (g : ℕ → ℝ) (x y : ℕ) :
    ∑ n ∈ Finset.Ioc x y, g n * weight k h R lam n =
      ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        lam d * lam e *
          (∑ n ∈ Finset.filter
            (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
            (Finset.Ioc x y), g n) := by
  classical
  have inner : ∀ d e : Fin k → ℕ,
      ∑ n ∈ Finset.Ioc x y,
          g n * ((if (∀ i, d i ∣ n + h i) then lam d else 0) *
            (if (∀ i, e i ∣ n + h i) then lam e else 0))
        = lam d * lam e *
          (∑ n ∈ Finset.filter
            (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
            (Finset.Ioc x y), g n) := by
    intro d e
    have h1 : ∀ n : ℕ,
        g n * ((if (∀ i, d i ∣ n + h i) then lam d else 0) *
          (if (∀ i, e i ∣ n + h i) then lam e else 0))
        = if (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i
          then lam d * lam e * g n else 0 := by
      intro n
      by_cases hd : (∀ i, d i ∣ n + h i) <;> by_cases he : (∀ i, e i ∣ n + h i)
      · rw [if_pos hd, if_pos he, if_pos ⟨hd, he⟩]; ring
      · rw [if_pos hd, if_neg he, if_neg (fun hh => he hh.2)]; simp
      · rw [if_neg hd, if_pos he, if_neg (fun hh => hd hh.1)]; simp
      · rw [if_neg hd, if_neg he, if_neg (fun hh => hd hh.1)]; simp
    rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.mul_sum,
      ← Finset.sum_filter]
  calc ∑ n ∈ Finset.Ioc x y, g n * weight k h R lam n
      = ∑ n ∈ Finset.Ioc x y, g n * (∑ d ∈ tupleSupport k R,
          ∑ e ∈ tupleSupport k R,
            (if (∀ i, d i ∣ n + h i) then lam d else 0) *
              (if (∀ i, e i ∣ n + h i) then lam e else 0)) :=
        Finset.sum_congr rfl (fun n _ => by rw [weight_expand])
    _ = ∑ n ∈ Finset.Ioc x y, ∑ d ∈ tupleSupport k R,
          ∑ e ∈ tupleSupport k R,
            g n * ((if (∀ i, d i ∣ n + h i) then lam d else 0) *
              (if (∀ i, e i ∣ n + h i) then lam e else 0)) := by
        apply Finset.sum_congr rfl
        intro n _
        simp only [Finset.mul_sum]
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          ∑ n ∈ Finset.Ioc x y,
            g n * ((if (∀ i, d i ∣ n + h i) then lam d else 0) *
              (if (∀ i, e i ∣ n + h i) then lam e else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          lam d * lam e *
            (∑ n ∈ Finset.filter
              (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
              (Finset.Ioc x y), g n) :=
        Finset.sum_congr rfl (fun d _ =>
          Finset.sum_congr rfl (fun e _ => inner d e))

/-- Single-prime joint count: summing the prime indicator at one coordinate
    over the joint-divisibility filter gives the prime-restricted count. -/
theorem sum_filter_joint_primeInd {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ}
    (i : Fin k) :
    ∑ n ∈ Finset.filter
      (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y), primeInd (n + h i)
      = ((Finset.filter
        (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
          Nat.Prime (n + h i))
        (Finset.Ioc x y)).card : ℝ) := by
  classical
  have hpi : ∀ n : ℕ, primeInd (n + h i) =
      if Nat.Prime (n + h i) then (1 : ℝ) else 0 := fun n => rfl
  rw [Finset.sum_congr rfl (fun n _ => hpi n), Finset.sum_boole,
    Finset.filter_filter]

/-- Prime-pair joint count: summing a product of two prime indicators over
    the joint-divisibility filter gives the doubly prime-restricted count. -/
theorem sum_filter_joint_primePair {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ}
    (i j : Fin k) :
    ∑ n ∈ Finset.filter
      (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y), primeInd (n + h i) * primeInd (n + h j)
      = ((Finset.filter
        (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
          (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)))
        (Finset.Ioc x y)).card : ℝ) := by
  classical
  have hpm : ∀ n : ℕ, primeInd (n + h i) * primeInd (n + h j) =
      if (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)) then (1 : ℝ) else 0 :=
    fun n => primeInd_mul _ _
  rw [Finset.sum_congr rfl (fun n _ => hpm n), Finset.sum_boole,
    Finset.filter_filter]

/-- Headline: the linear second moment interchanged into prime-weighted
    joint counts. Only single-prime counts appear; there are no i ≠ j
    prime-pair terms in the linear form. -/
theorem secondMoment_eq (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) :
    secondMoment k h R lam x y =
      ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        lam d * lam e *
          (∑ i, ((Finset.filter
            (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
              Nat.Prime (n + h i))
            (Finset.Ioc x y)).card : ℝ)) := by
  classical
  unfold secondMoment
  rw [weightedSum_interchange]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  have inner : ∑ n ∈ Finset.filter
        (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
        (Finset.Ioc x y), ∑ i, primeInd (n + h i)
      = ∑ i, ((Finset.filter
        (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
          Nat.Prime (n + h i))
        (Finset.Ioc x y)).card : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => sum_filter_joint_primeInd i)
  exact inner

/-- CRT residue characterization of joint divisibility: given a particular
    solution `a` of the system, the system is equivalent to the single
    residue class `n ≡ a` modulo the lcm of the moduli. Forward via
    per-coordinate ModEq then `modEq_finset_lcm`; backward via
    `Finset.dvd_lcm` and `Nat.ModEq.of_dvd`. -/
theorem jointDivisibility_iff_modEq_lcm {k : ℕ} {m h : Fin k → ℕ}
    (a : ℕ) (ha : ∀ i, m i ∣ a + h i) (n : ℕ) :
    (∀ i, m i ∣ n + h i) ↔ n ≡ a [MOD Finset.lcm Finset.univ m] := by
  constructor
  · intro hn
    have hmod : ∀ i, n ≡ a [MOD m i] := fun i => by
      have h1 : n + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (hn i)
      have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
      exact Nat.ModEq.add_right_cancel' (h i) (h1.trans h2.symm)
    exact modEq_finset_lcm Finset.univ (fun i _ => hmod i)
  · intro hn i
    have hmi : m i ∣ Finset.lcm Finset.univ m := Finset.dvd_lcm (Finset.mem_univ i)
    have hmod : n ≡ a [MOD m i] := Nat.ModEq.of_dvd hmi hn
    have h1 : n + h i ≡ a + h i [MOD m i] := hmod.add_right (h i)
    have h2 : a + h i ≡ 0 [MOD m i] := Nat.modEq_zero_iff_dvd.mpr (ha i)
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)

/-- Incompatible vanishing for the prime-restricted count: if some pair of
    shifts is incompatible mod the gcd of their coordinatewise lcms, then
    the joint-divisibility filter is empty (by `count_twoTuple_eq_zero`),
    hence the prime-restricted subfilter at any fixed coordinate is empty
    and its count is 0. -/
theorem primeCount_eq_zero_of_incompatible {k : ℕ} {d e h : Fin k → ℕ}
    {x y : ℕ} (t : Fin k)
    (hincompat : ∃ i j, ¬ (h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i))
      (Nat.lcm (d j) (e j))])) :
    (Finset.filter
      (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
        Nat.Prime (n + h t))
      (Finset.Ioc x y)).card = 0 := by
  classical
  have hz := count_twoTuple_eq_zero (k := k) (d := d) (e := e) (h := h)
    (x := x) (y := y) hincompat
  have hempty : (Finset.filter
      (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y)) = ∅ := Finset.card_eq_zero.mp hz
  rw [Finset.card_eq_zero]
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨hmem, hj, -⟩ := h
  have hjn : n ∈ Finset.filter
      (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
      (Finset.Ioc x y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hmem, hj⟩
  rw [hempty] at hjn
  exact Finset.notMem_empty n hjn

/-- Squared-variant split: the squared second moment equals the double sum
    over support pairs of lam d · lam e times (the single-prime counts plus,
    for each i, the prime-pair counts over j ≠ i). The diagonal terms use
    primeInd² = primeInd; the off-diagonal terms are genuine prime-pair
    counts. -/
theorem secondMomentSq_split (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) :
    secondMomentSq k h R lam x y =
      ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        lam d * lam e *
          (∑ i, ((Finset.filter
            (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
              Nat.Prime (n + h i))
            (Finset.Ioc x y)).card : ℝ)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, ((Finset.filter
            (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
              (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)))
            (Finset.Ioc x y)).card : ℝ)) := by
  classical
  have inner : ∀ d e : Fin k → ℕ,
      ∑ n ∈ Finset.filter
        (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
        (Finset.Ioc x y), (∑ i, primeInd (n + h i)) ^ 2
      = ∑ i, ((Finset.filter
        (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
          Nat.Prime (n + h i))
        (Finset.Ioc x y)).card : ℝ)
        + ∑ i, ∑ j ∈ Finset.univ.erase i, ((Finset.filter
        (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
          (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)))
        (Finset.Ioc x y)).card : ℝ) := by
    intro d e
    have hdiag : ∀ i : Fin k,
        ∑ n ∈ Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y), primeInd (n + h i) * primeInd (n + h i)
        = ((Finset.filter
          (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
            Nat.Prime (n + h i))
          (Finset.Ioc x y)).card : ℝ) := by
      intro i
      rw [Finset.sum_congr rfl (fun n _ => primeInd_sq (n + h i))]
      exact sum_filter_joint_primeInd i
    calc ∑ n ∈ Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y), (∑ i, primeInd (n + h i)) ^ 2
        = ∑ n ∈ Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y), ∑ i, ∑ j, primeInd (n + h i) * primeInd (n + h j) :=
          Finset.sum_congr rfl (fun n _ => by rw [pow_two, Finset.sum_mul_sum])
      _ = ∑ i, ∑ j, ∑ n ∈ Finset.filter
          (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
          (Finset.Ioc x y), primeInd (n + h i) * primeInd (n + h j) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, (((Finset.filter
          (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
            Nat.Prime (n + h i))
          (Finset.Ioc x y)).card : ℝ)
          + ∑ j ∈ Finset.univ.erase i, ((Finset.filter
          (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
            (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)))
          (Finset.Ioc x y)).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          have hsplit := (Finset.add_sum_erase Finset.univ
            (fun j => ∑ n ∈ Finset.filter
              (fun n => (∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i)
              (Finset.Ioc x y), primeInd (n + h i) * primeInd (n + h j))
            (Finset.mem_univ i)).symm
          rw [hsplit, hdiag i]
          congr 1
          exact Finset.sum_congr rfl
            (fun j _ => sum_filter_joint_primePair i j)
      _ = ∑ i, ((Finset.filter
          (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
            Nat.Prime (n + h i))
          (Finset.Ioc x y)).card : ℝ)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, ((Finset.filter
          (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
            (Nat.Prime (n + h i) ∧ Nat.Prime (n + h j)))
          (Finset.Ioc x y)).card : ℝ) :=
          Finset.sum_add_distrib
  unfold secondMomentSq
  rw [weightedSum_interchange]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  rw [inner d e]


/-! ### Prime counts in residue classes -/

/-- Primes `p ≤ Y` with `p ≡ r [MOD L]`: the local analogue of the
    platform's `primeCountingAP Y L r`. -/
noncomputable def primeCountAP (Y L r : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card

/-- The prime count in a residue class depends only on the class mod `L`. -/
theorem primeCountAP_eq_of_modEq {Y L r r' : ℕ} (h : r ≡ r' [MOD L]) :
    primeCountAP Y L r = primeCountAP Y L r' := by
  have hset : (Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])
      = (Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r' [MOD L]) := by
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hp, hpr⟩
      exact ⟨hp, hpr.trans h⟩
    · rintro ⟨hp, hpr⟩
      exact ⟨hp, hpr.trans h.symm⟩
  unfold primeCountAP
  rw [hset]

/-- An interval prime count is a difference of `primeCountAP` counts:
    primes in (a, b] in a class = (primes ≤ b) − (primes ≤ a). -/
theorem intervalPrimeCount_eq_primeCountAP_sub (a b L r : ℕ) (hab : a ≤ b) :
    ((Finset.filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L]) (Finset.Ioc a b)).card : ℝ)
      = (primeCountAP b L r : ℝ) - (primeCountAP a L r : ℝ) := by
  classical
  have hunion : (Finset.range (b + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])
      = (Finset.range (a + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])
        ∪ (Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L]) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨hpb, hP⟩
      by_cases hpa : p < a + 1
      · exact Or.inl ⟨hpa, hP⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hP⟩
    · rintro (⟨hpa, hP⟩ | ⟨⟨hap, hpb⟩, hP⟩)
      · exact ⟨by omega, hP⟩
      · exact ⟨by omega, hP⟩
  have hdisj : Disjoint ((Finset.range (a + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L]))
      ((Finset.Ioc a b).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter, Finset.mem_range] at hp1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp2
    obtain ⟨hpa, -⟩ := hp1
    obtain ⟨⟨hap, -⟩, -⟩ := hp2
    omega
  have hcard : primeCountAP b L r
      = primeCountAP a L r
        + (Finset.filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L]) (Finset.Ioc a b)).card := by
    unfold primeCountAP
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hcast : (primeCountAP b L r : ℝ)
      = (primeCountAP a L r : ℝ)
        + ((Finset.filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L]) (Finset.Ioc a b)).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-! ### Joint-divisibility reformulation -/

/-- The two-tuple joint divisibility condition is a single condition with
    the coordinatewise lcms as moduli. -/
theorem joint_iff_lcm {k : ℕ} {d e h : Fin k → ℕ} {n : ℕ} :
    ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j)
      ↔ ∀ j, Nat.lcm (d j) (e j) ∣ n + h j := by
  constructor
  · rintro ⟨hd, he⟩ j
    have hle := lcm_dvd (hd j) (he j)
    rwa [lcm_eq_nat_lcm] at hle
  · intro hm
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have hle := dvd_lcm_left (d j) (e j)
      rw [lcm_eq_nat_lcm] at hle
      exact Nat.dvd_trans hle (hm j)
    · have hle := dvd_lcm_right (d j) (e j)
      rw [lcm_eq_nat_lcm] at hle
      exact Nat.dvd_trans hle (hm j)

/-- Reindexing: the joint prime count at coordinate `i` equals the count
    of primes `p` in (x + h i, y + h i] with `p ≡ w + h i [MOD L]`, where
    `w` is a witness of the joint system and `L` is the lcm of the
    coordinatewise lcms. The map is `n ↦ n + h i`. -/
theorem jointPrimeCount_eq_intervalPrimeCount {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ}
    (i : Fin k) (w : ℕ) (hw : ∀ j, Nat.lcm (d j) (e j) ∣ w + h j) :
    ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y)).card)
      = ((Finset.filter (fun p => Nat.Prime p ∧ p ≡ w + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))]) (Finset.Ioc (x + h i) (y + h i))).card) := by
  classical
  have hset : (Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y))
      = Finset.filter (fun n => n ≡ w [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))] ∧ Nat.Prime (n + h i)) (Finset.Ioc x y) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨hj, hp⟩
      exact ⟨(jointDivisibility_iff_modEq_lcm w hw n).mp (joint_iff_lcm.mp hj), hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨joint_iff_lcm.mpr ((jointDivisibility_iff_modEq_lcm w hw n).mpr hn), hp⟩
  rw [hset]
  refine Finset.card_bij' (fun n _ => n + h i) (fun p _ => p - h i) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnI, hnmod, hnp⟩ := hn
    refine ⟨?_, hnp, hnmod.add_right (h i)⟩
    rw [Finset.mem_Ioc] at hnI ⊢
    obtain ⟨hxn, hny⟩ := hnI
    exact ⟨by omega, by omega⟩
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpI, hpp, hpmod⟩ := hp
    rw [Finset.mem_Ioc] at hpI ⊢
    obtain ⟨hxp, hpy⟩ := hpI
    have hle : h i ≤ p := by omega
    refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
    · have h1 : (p - h i) + h i ≡ w + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))] := by
        rw [Nat.sub_add_cancel hle]
        exact hpmod
      exact Nat.ModEq.add_right_cancel' (h i) h1
    · rw [Nat.sub_add_cancel hle]
      exact hpp
  · intro n _
    exact Nat.add_sub_cancel n (h i)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hxp, -⟩, -⟩ := hp
    exact Nat.sub_add_cancel (by omega : h i ≤ p)

/-! ### The collapse: non-coprime classes hold at most one prime -/

/-- Collapse: if the class `w + h i` mod `L` is not coprime to `L`, then
    the joint prime count at coordinate `i` is at most 1. Proof: pick a
    prime `q` dividing `gcd (w + h i) L`; every prime `p` in the class is
    divisible by `q` (since `q ∣ L` and `q ∣ w + h i`), hence equals `q`,
    so all `n` in the filter satisfy `n + h i = q`. In particular, when
    `m i > 1` the count is ≤ 1, since `m i` divides both `w + h i` and
    `L`. -/
theorem jointPrimeCount_le_one_of_not_coprime {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ}
    (i : Fin k) (w : ℕ) (hw : ∀ j, Nat.lcm (d j) (e j) ∣ w + h j)
    (hncop : ¬ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y)).card) ≤ 1 := by
  classical
  have hgcd : Nat.gcd (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ≠ 1 :=
    fun hg => hncop (Nat.coprime_iff_gcd_eq_one.mpr hg)
  obtain ⟨q, hqprime, hqdv⟩ := Nat.exists_prime_and_dvd hgcd
  have hqL : q ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    Nat.dvd_trans hqdv (Nat.gcd_dvd_right _ _)
  have hqw : q ∣ w + h i := Nat.dvd_trans hqdv (Nat.gcd_dvd_left _ _)
  rw [Finset.card_le_one]
  intro n₁ hn₁ n₂ hn₂
  have key : ∀ n : ℕ, n ∈ Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y) → n + h i = q := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hj, hp⟩ := hn
    have hnmod : n ≡ w [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))] :=
      (jointDivisibility_iff_modEq_lcm w hw n).mp (joint_iff_lcm.mp hj)
    have h1 : n + h i ≡ w + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))] :=
      hnmod.add_right (h i)
    have h2 : n + h i ≡ w + h i [MOD q] := Nat.ModEq.of_dvd hqL h1
    have h3 : n + h i ≡ 0 [MOD q] := h2.trans (Nat.modEq_zero_iff_dvd.mpr hqw)
    have h4 : q ∣ n + h i := Nat.modEq_zero_iff_dvd.mp h3
    exact ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp h4).symm
  have e1 := key n₁ hn₁
  have e2 := key n₂ hn₂
  exact Nat.add_right_cancel (e1.trans e2.symm)

/-! ### Per-triple approximation against an abstract model -/

/-- Per-triple approximation: the joint prime count at coordinate `i`
    equals the model difference `M (y + h i) L - M (x + h i) L` up to the
    two model errors at the interval endpoints. No coprimality is needed
    for this identity — it is the reindexing plus the interval/difference
    computation. -/
theorem jointPrimeCount_approx (M : ℕ → ℕ → ℝ) {k : ℕ} {d e h : Fin k → ℕ} {x y : ℕ}
    (i : Fin k) (w : ℕ) (hw : ∀ j, Nat.lcm (d j) (e j) ∣ w + h j) (hxy : x ≤ y) :
    abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y)).card : ℝ)
      - (M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
        - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
    ≤ abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ)
        - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ)
        - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by
  have hcount : ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h i)) (Finset.Ioc x y)).card : ℝ)
      = (primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ)
        - (primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ) := by
    rw [jointPrimeCount_eq_intervalPrimeCount i w hw]
    exact intervalPrimeCount_eq_primeCountAP_sub (x + h i) (y + h i)
      (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) (by omega)
  rw [hcount]
  set A := (primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ)
  set B := (primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h i) : ℝ)
  set C := M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
  set D := M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
  have heq : (A - B) - (C - D) = (A - C) - (B - D) := by ring
  rw [heq]
  have heq2 : (A - C) - (B - D) = (A - C) + (-(B - D)) := sub_eq_add_neg _ _
  rw [heq2]
  have habs := abs_add_le (A - C) (-(B - D))
  rw [abs_neg] at habs
  exact habs

/-! ### The BV-ready main term and error bound -/

/-- A support pair `(d, e)` is GOOD at coordinate `i` when some witness
    `w` of the joint system has `w + h i` coprime to `L`: exactly the
    case where BV's main term `li/φ(L)` can describe the prime count.
    Bad pairs have count ≤ 1 by the collapse lemma. -/
def goodPair {k : ℕ} (h d e : Fin k → ℕ) (i : Fin k) : Prop :=
  ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))

/-- The summed model error over ALL residues mod `L` at height `Y`.
    Summing over all residues (not just coprime ones) keeps the statement
    witness-free and needs no coprimality transport; it costs at most a
    factor `L` against the max-residue form BV bounds, which the future
    error-control lemma will work with directly. -/
noncomputable def bvErrSum (M : ℕ → ℕ → ℝ) (Y L : ℕ) : ℝ :=
  ∑ r ∈ Finset.range L, abs ((primeCountAP Y L r : ℝ) - M Y L)

/-- Main-term summand for one triple: the model difference at the
    interval endpoints for good pairs, 0 for bad pairs. -/
noncomputable def bvMainSummand (M : ℕ → ℕ → ℝ) {k : ℕ} (h d e : Fin k → ℕ)
    (i : Fin k) (x y : ℕ) : ℝ := by
  classical
  exact if goodPair h d e i then
    M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
      - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
    else 0

/-- Error summand for one triple: the summed model errors at both
    endpoints for good pairs, 1 for bad pairs (the collapse bound). -/
noncomputable def bvErrSummand (M : ℕ → ℕ → ℝ) {k : ℕ} (h d e : Fin k → ℕ)
    (i : Fin k) (x y : ℕ) : ℝ := by
  classical
  exact if goodPair h d e i then
    bvErrSum M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
      + bvErrSum M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
    else 1

/-- The BV main term for the second moment: `λ_d λ_e` times the model
    difference, summed over support pairs and coordinates (bad pairs
    contribute 0). -/
noncomputable def bvMainTerm (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (x y : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    lam d * lam e * (∑ i, bvMainSummand M h d e i x y)

/-- The BV error bound for the second moment: `|λ_d λ_e|` times the
    per-triple error summand, summed over support pairs and coordinates. -/
noncomputable def bvErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (x y : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    abs (lam d * lam e) * (∑ i, bvErrSummand M h d e i x y)

/-- Headline: the second-moment BV evaluation. For ANY model `M` and
    `x ≤ y`, the linear second moment `S₂` equals the BV main term up
    to the BV error bound. Incompatible pairs contribute exactly 0 to
    both sides (their prime counts vanish); bad compatible pairs
    contribute at most `|λ_d λ_e|` (collapse); good pairs contribute
    their model errors, summed over all residues mod `L`. -/
theorem secondMoment_bvMainTerm (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ bvErrBound k h R lam M x y := by
  classical
  have per_i : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R, ∀ t,
      abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
        - bvMainSummand M h d e t x y) ≤ bvErrSummand M h d e t x y := by
    intro d hd e he t
    have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
    have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
    have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
      intro j
      apply Nat.lcm_ne_zero
      · have hj1 := hd1 j
        omega
      · have hj2 := he1 j
        omega
    have hLpos : 0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
      Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun j _ => hmne j))
    by_cases hgood : goodPair h d e t
    · unfold bvMainSummand bvErrSummand
      rw [if_pos hgood, if_pos hgood]
      obtain ⟨w, hw, -⟩ := hgood
      have happ := jointPrimeCount_approx M t w hw hxy
      refine le_trans happ (add_le_add ?_ ?_)
      · unfold bvErrSum
        have hmem : (w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
          Finset.mem_range.mpr (Nat.mod_lt _ hLpos)
        have hle := Finset.single_le_sum
          (fun r _ => abs_nonneg ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ) - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
          hmem
        have hle' : abs ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ((w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) : ℝ)
            - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            ≤ ∑ r ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))),
              abs ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ)
                - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := hle
        rwa [primeCountAP_eq_of_modEq (Nat.mod_modEq (w + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))] at hle'
      · unfold bvErrSum
        have hmem : (w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
          Finset.mem_range.mpr (Nat.mod_lt _ hLpos)
        have hle := Finset.single_le_sum
          (fun r _ => abs_nonneg ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ) - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
          hmem
        have hle' : abs ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ((w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) : ℝ)
            - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            ≤ ∑ r ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))),
              abs ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ)
                - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := hle
        rwa [primeCountAP_eq_of_modEq (Nat.mod_modEq (w + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))] at hle'
    · by_cases hcomp : (∀ i' j', h i' ≡ h j' [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))])
      · obtain ⟨w₀, hw₀⟩ := exists_dvd_of_compatible (m := fun j => Nat.lcm (d j) (e j)) hmne hcomp
        have hgcd : Nat.gcd (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ≠ 1 := by
          intro hg
          exact hgood ⟨w₀, hw₀, Nat.coprime_iff_gcd_eq_one.mpr hg⟩
        have hncop : ¬ Nat.Coprime (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
          fun hc => hgcd (Nat.coprime_iff_gcd_eq_one.mp hc)
        have hle := jointPrimeCount_le_one_of_not_coprime (x := x) (y := y) t w₀ hw₀ hncop
        unfold bvMainSummand bvErrSummand
        rw [if_neg hgood, if_neg hgood]
        rw [sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hle
      · push_neg at hcomp
        obtain ⟨i₀, j₀, hij⟩ := hcomp
        have hzero := primeCount_eq_zero_of_incompatible (x := x) (y := y) t ⟨i₀, j₀, hij⟩
        unfold bvMainSummand bvErrSummand
        rw [if_neg hgood, if_neg hgood, hzero]
        simp
  have per_pair : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, bvErrSummand M h d e t x y) := by
    intro d hd e he
    have heq : lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)
        = lam d * lam e * (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [heq, abs_mul]
    calc abs (lam d * lam e) * abs (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ abs (lam d * lam e) * (∑ t, bvErrSummand M h d e t x y) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => per_i d hd e he t)) (abs_nonneg _)
  rw [secondMoment_eq]
  unfold bvMainTerm bvErrBound
  simp only [← Finset.sum_sub_distrib]
  calc abs (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)))
      ≤ ∑ d ∈ tupleSupport k R, abs (∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)) :=
        Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * (∑ t, bvErrSummand M h d e t x y) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => per_pair d hd e he))


/-! ### Level: the combined modulus is at most R² -/

/-- The combined modulus `L` of a support pair is at most `R²`: each
    coordinatewise lcm is at most the product of the coordinates, the
    lcm of the coordinates divides (hence is at most) their product,
    and the product splits as (∏ d j)(∏ e j) ≤ R * R. -/
theorem lcm_le_sq_of_mem_support {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) (he : e ∈ tupleSupport k R) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≤ R ^ 2 := by
  classical
  have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
  have hdprod : ∏ j, d j ≤ R := (mem_tupleSupport.mp hd).2.2
  have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
  have heprod : ∏ j, e j ≤ R := (mem_tupleSupport.mp he).2.2
  have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
    intro j
    apply Nat.lcm_ne_zero
    · have h1 := hd1 j
      omega
    · have h2 := he1 j
      omega
  have hprodpos : 0 < ∏ j, Nat.lcm (d j) (e j) :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hmne j))
  have hdvd : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ∣ ∏ j, Nat.lcm (d j) (e j) :=
    Finset.lcm_dvd (fun j _ => Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  have hle1 : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) :=
    Nat.le_of_dvd hprodpos hdvd
  have hle2 : ∏ j, Nat.lcm (d j) (e j) ≤ ∏ j, (d j * e j) := by
    apply Finset.prod_le_prod'
    intro j _
    have h1 : GCDMonoid.lcm (d j) (e j) ∣ d j * e j :=
      lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _)
    rw [lcm_eq_nat_lcm] at h1
    exact Nat.le_of_dvd (mul_pos (by have h := hd1 j; omega) (by have h := he1 j; omega)) h1
  have hle3 : ∏ j, (d j * e j) = (∏ j, d j) * (∏ j, e j) := Finset.prod_mul_distrib
  have hle4 : (∏ j, d j) * (∏ j, e j) ≤ R * R := Nat.mul_le_mul hdprod heprod
  calc Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) := hle1
    _ ≤ ∏ j, (d j * e j) := hle2
    _ = (∏ j, d j) * (∏ j, e j) := hle3
    _ ≤ R * R := hle4
    _ = R ^ 2 := (pow_two R).symm

/-! ### Coprime-restricted error sums -/

/-- The summed model error over COPRIME residues mod `L` at height `Y`.
    This is the operative error sum for BV (see the header): BV controls
    coprime residues, not the non-coprime ones against `li/φ`. -/
noncomputable def bvErrSumCoprime (M : ℕ → ℕ → ℝ) (Y L : ℕ) : ℝ :=
  ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
    abs ((primeCountAP Y L r : ℝ) - M Y L)

/-- Error summand for one triple, coprime version: summed coprime model
    errors at both endpoints for good pairs, 1 for bad pairs. -/
noncomputable def bvErrSummandCoprime (M : ℕ → ℕ → ℝ) {k : ℕ} (h d e : Fin k → ℕ)
    (i : Fin k) (x y : ℕ) : ℝ := by
  classical
  exact if goodPair h d e i then
    bvErrSumCoprime M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
      + bvErrSumCoprime M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
    else 1

/-- The coprime BV error bound for the second moment: `|λ_d λ_e|` times
    the per-triple coprime error summand, summed over support pairs and
    coordinates. -/
noncomputable def bvErrBoundCoprime (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (x y : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    abs (lam d * lam e) * (∑ i, bvErrSummandCoprime M h d e i x y)

/-! ### Variant headline: the second-moment bound against the coprime error -/

/-- Headline variant: the linear second moment `S₂` equals the BV main
    term up to the COPRIME error bound. Same proof shape as
    `secondMoment_bvMainTerm`, with `single_le_sum` over the coprime
    filter instead of the full range: for a good pair, the witness
    residue `(w + h t) % L` is itself coprime to `L` (gcd is preserved
    under mod), so it is a term of the coprime sum. -/
theorem secondMoment_bvMainTerm_coprime (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ bvErrBoundCoprime k h R lam M x y := by
  classical
  have per_i : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R, ∀ t,
      abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
        - bvMainSummand M h d e t x y) ≤ bvErrSummandCoprime M h d e t x y := by
    intro d hd e he t
    have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
    have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
    have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
      intro j
      apply Nat.lcm_ne_zero
      · have hj1 := hd1 j
        omega
      · have hj2 := he1 j
        omega
    have hLpos : 0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
      Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun j _ => hmne j))
    by_cases hgood : goodPair h d e t
    · unfold bvMainSummand bvErrSummandCoprime
      rw [if_pos hgood, if_pos hgood]
      obtain ⟨w, hw, hcop⟩ := hgood
      have happ := jointPrimeCount_approx M t w hw hxy
      refine le_trans happ (add_le_add ?_ ?_)
      · unfold bvErrSumCoprime
        have hmem : (w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter
              (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hLpos, ?_⟩
          rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
          rw [← Nat.gcd_rec (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h t),
            Nat.gcd_comm (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h t)]
          exact hcop
        have hle := Finset.single_le_sum
          (fun r _ => abs_nonneg ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ) - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
          hmem
        have hle' : abs ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ((w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) : ℝ)
            - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            ≤ ∑ r ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))),
              abs ((primeCountAP (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ)
                - M (y + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := hle
        rwa [primeCountAP_eq_of_modEq (Nat.mod_modEq (w + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))] at hle'
      · unfold bvErrSumCoprime
        have hmem : (w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter
              (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hLpos, ?_⟩
          rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
          rw [← Nat.gcd_rec (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h t),
            Nat.gcd_comm (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (w + h t)]
          exact hcop
        have hle := Finset.single_le_sum
          (fun r _ => abs_nonneg ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ) - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
          hmem
        have hle' : abs ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ((w + h t) % (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) : ℝ)
            - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            ≤ ∑ r ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))),
              abs ((primeCountAP (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ)
                - M (x + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := hle
        rwa [primeCountAP_eq_of_modEq (Nat.mod_modEq (w + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))] at hle'
    · by_cases hcomp : (∀ i' j', h i' ≡ h j' [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))])
      · obtain ⟨w₀, hw₀⟩ := exists_dvd_of_compatible (m := fun j => Nat.lcm (d j) (e j)) hmne hcomp
        have hgcd : Nat.gcd (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ≠ 1 := by
          intro hg
          exact hgood ⟨w₀, hw₀, Nat.coprime_iff_gcd_eq_one.mpr hg⟩
        have hncop : ¬ Nat.Coprime (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
          fun hc => hgcd (Nat.coprime_iff_gcd_eq_one.mp hc)
        have hle := jointPrimeCount_le_one_of_not_coprime (x := x) (y := y) t w₀ hw₀ hncop
        unfold bvMainSummand bvErrSummandCoprime
        rw [if_neg hgood, if_neg hgood]
        rw [sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hle
      · push_neg at hcomp
        obtain ⟨i₀, j₀, hij⟩ := hcomp
        have hzero := primeCount_eq_zero_of_incompatible (x := x) (y := y) t ⟨i₀, j₀, hij⟩
        unfold bvMainSummand bvErrSummandCoprime
        rw [if_neg hgood, if_neg hgood, hzero]
        simp
  have per_pair : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, bvErrSummandCoprime M h d e t x y) := by
    intro d hd e he
    have heq : lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)
        = lam d * lam e * (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [heq, abs_mul]
    calc abs (lam d * lam e) * abs (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ abs (lam d * lam e) * (∑ t, bvErrSummandCoprime M h d e t x y) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => per_i d hd e he t)) (abs_nonneg _)
  rw [secondMoment_eq]
  unfold bvMainTerm bvErrBoundCoprime
  simp only [← Finset.sum_sub_distrib]
  calc abs (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)))
      ≤ ∑ d ∈ tupleSupport k R, abs (∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)) :=
        Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * (∑ t, bvErrSummandCoprime M h d e t x y) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => per_pair d hd e he))

/-! ### Argmax bridge: from a BV sum bound to a pointwise coprime bound -/

/-- Argmax bridge: if a BV-style sum bound holds for EVERY coprime
    choice function `v` (the form of the platform BV record, one residue
    per modulus), then every coprime residue at every modulus in the
    sum range satisfies the same bound pointwise. Proof: given `L` in
    the range and a coprime residue `r`, apply the hypothesis to the
    choice function that is `r` at `L` and `1` elsewhere (1 is coprime
    to everything), and bound the `L`-term of the sum by the whole sum.
    No real analysis and no `li` are involved: the sum range `S` and
    the bound `B` are abstract. The instantiation lemma supplies
    `S` = the BV range and `B` = `C * Y * log Y ^ (-A')`. -/
theorem maxCoprimeErr_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y : ℕ) (S : Finset ℕ) (B : ℝ)
    (hB : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ S, abs ((primeCountAP Y q (v q) : ℝ) - M Y q) ≤ B)
    {L : ℕ} (hL : L ∈ S) {r : ℕ} (hr : Nat.Coprime r L) :
    abs ((primeCountAP Y L r : ℝ) - M Y L) ≤ B := by
  classical
  have hvcop : ∀ q, Nat.Coprime (Function.update (fun _ => 1) L r q) q := by
    intro q
    by_cases hq : q = L
    · subst hq
      rw [Function.update_self]
      exact hr
    · rw [Function.update_of_ne hq]
      exact Nat.coprime_one_left q
  have hsum := hB (Function.update (fun _ => 1) L r) hvcop
  have hle := Finset.single_le_sum
    (fun q _ => abs_nonneg ((primeCountAP Y q (Function.update (fun _ => 1) L r q) : ℝ) - M Y q))
    hL
  rw [Function.update_self] at hle
  exact le_trans hle hsum

/-! ### Error control: the coprime bound in terms of λ-mass and level -/

/-- Error control: under a pointwise coprime-residue bound `hErr` (the
    BV-max input, to be discharged by the instantiation lemma) and
    nonnegativity of `E`, the coprime error bound is at most the
    λ-mass Λ times (R² times the summed endpoint errors, plus one per
    coordinate for the bad pairs). The λ-mass is an explicit factor,
    not a hypothesis; the crude steps are card ≤ L (coprime residues
    are a subset of all residues) and L ≤ R² (the level lemma). -/
theorem bvErrBoundCoprime_le {k : ℕ} {h : Fin k → ℕ} {R : ℕ}
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (E : ℕ → ℝ) {x y : ℕ}
    (hE : ∀ Y, 0 ≤ E Y)
    (hErr : ∀ Y L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs ((primeCountAP Y L r : ℝ) - M Y L) ≤ E Y) :
    bvErrBoundCoprime k h R lam M x y
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
        * ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) := by
  classical
  have per_triple : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R, ∀ i,
      bvErrSummandCoprime M h d e i x y
        ≤ (R : ℝ) ^ 2 * (E (y + h i) + E (x + h i)) + 1 := by
    intro d hd e he i
    have hL : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≤ R ^ 2 :=
      lcm_le_sq_of_mem_support hd he
    by_cases hgood : goodPair h d e i
    · unfold bvErrSummandCoprime
      rw [if_pos hgood]
      have hbound : ∀ Y : ℕ, bvErrSumCoprime M Y (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
          ≤ (R : ℝ) ^ 2 * E Y := by
        intro Y
        unfold bvErrSumCoprime
        calc ∑ r ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))),
              abs ((primeCountAP Y (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) r : ℝ) - M Y (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            ≤ ∑ r ∈ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))), E Y := by
              apply Finset.sum_le_sum
              intro r hr
              rw [Finset.mem_filter] at hr
              exact hErr Y _ r hL hr.2
          _ = (((Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))).card : ℝ) * E Y := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) * E Y := by
              have hcard : ((Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))).card
                  ≤ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := by
                calc ((Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).filter (fun r => Nat.Coprime r (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))).card
                    ≤ (Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))).card :=
                    Finset.card_filter_le _ _
                  _ = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := Finset.card_range _
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hE Y)
          _ ≤ (R : ℝ) ^ 2 * E Y := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL) (hE Y)
      calc bvErrSumCoprime M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            + bvErrSumCoprime M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
          ≤ (R : ℝ) ^ 2 * E (y + h i) + (R : ℝ) ^ 2 * E (x + h i) :=
          add_le_add (hbound _) (hbound _)
        _ = (R : ℝ) ^ 2 * (E (y + h i) + E (x + h i)) := by ring
        _ ≤ (R : ℝ) ^ 2 * (E (y + h i) + E (x + h i)) + 1 := le_add_of_nonneg_right zero_le_one
    · unfold bvErrSummandCoprime
      rw [if_neg hgood]
      have hnonneg : 0 ≤ (R : ℝ) ^ 2 * (E (y + h i) + E (x + h i)) :=
        mul_nonneg (by positivity) (add_nonneg (hE _) (hE _))
      linarith
  unfold bvErrBoundCoprime
  calc ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * (∑ i, bvErrSummandCoprime M h d e i x y)
      ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc ∑ i, bvErrSummandCoprime M h d e i x y
            ≤ ∑ i, ((R : ℝ) ^ 2 * (E (y + h i) + E (x + h i)) + 1) :=
            Finset.sum_le_sum (fun i _ => per_triple d hd e he i)
          _ = (R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ = (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
        * ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) := by
        simp only [← Finset.sum_mul]

/-! ### Combined corollary: the second moment with a controlled error -/

/-- Combined corollary (the submission candidate): under the BV-max
    input `hErr`, the second moment equals the BV main term up to
    λ-mass times (R² times the summed endpoint errors, plus one per
    coordinate for the bad pairs). -/
theorem secondMoment_bvErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (E : ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (hE : ∀ Y, 0 ≤ E Y)
    (hErr : ∀ Y L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs ((primeCountAP Y L r : ℝ) - M Y L) ≤ E Y) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
        * ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) :=
  le_trans (secondMoment_bvMainTerm_coprime k h R lam M hxy)
    (bvErrBoundCoprime_le lam M E hE hErr)


/-! ### Range membership: moduli at most R² lie in the BV range -/

/-- A modulus `L` with `1 ≤ L ≤ R²` lies in the BV range
    `(range ⌈Y^(1/2-η)⌉₊).filter (1 ≤ q ∧ (q:ℝ) < Y^(1/2-η))`
    whenever the level constraint `(R:ℝ)^2 < Y^(1/2-η)` holds: the
    real bound `(L:ℝ) < Y^(1/2-η)` follows from `L ≤ R²`, and the
    range membership follows from that real bound via `Nat.le_ceil`. -/
theorem mem_bvRange_of_le_sq {Y R L : ℕ} {η : ℝ}
    (hL1 : 1 ≤ L) (hLR : L ≤ R ^ 2)
    (hlevel : (R : ℝ) ^ 2 < (Y : ℝ) ^ (1 / 2 - η)) :
    L ∈ (Finset.range ⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊).filter
      (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ) ^ (1 / 2 - η)) := by
  have hle : (L : ℝ) ≤ (R : ℝ) ^ 2 := by
    have h : (L : ℝ) ≤ ((R ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hLR
    push_cast at h
    exact h
  have hlt : (L : ℝ) < (Y : ℝ) ^ (1 / 2 - η) := lt_of_le_of_lt hle hlevel
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hL1, hlt⟩
  have hceil : (L : ℝ) < ((⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le hlt (Nat.le_ceil _)
  exact_mod_cast hceil

/-! ### The instantiation lemma: a BV sum bound gives the pointwise bound -/

/-- Instantiation lemma: under a BV-style sum bound at height `Y`
    (for every coprime choice function, the summed coprime-residue
    model errors over the BV range are at most `B`) and the level
    constraint `(R:ℝ)^2 < Y^(1/2-η)`, every coprime-residue model
    error at modulus `L ≤ R²` is at most `B`. The model `li` is
    abstract here; at application time it is the logarithmic integral
    (see the header: the platform `logIntegral` is the Mathlib
    interval integral `∫ t in 2..Y, 1 / log t`). -/
theorem hErr_of_bvSumBound {R Y : ℕ} {η : ℝ} {li : ℝ → ℝ} {B : ℝ}
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y q (v q) : ℝ) - li (Y : ℝ) / (Nat.totient q : ℝ)) ≤ B)
    (hlevel : (R : ℝ) ^ 2 < (Y : ℝ) ^ (1 / 2 - η)) :
    ∀ L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs ((primeCountAP Y L r : ℝ) - li (Y : ℝ) / (Nat.totient L : ℝ)) ≤ B := by
  intro L r hLR hr
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · -- Degenerate modulus: coprime forces r = 1, the count is 0
    -- (no prime equals 1), and φ(0) = 0 kills the model term.
    subst hL0
    have hr1 : r = 1 := (Nat.coprime_zero_right r).mp hr
    subst hr1
    have hcount : primeCountAP Y 0 1 = 0 := by
      unfold primeCountAP
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro p _
      rintro ⟨hprime, hmod⟩
      have hp1 : p = 1 := by
        have h2 : p % 0 = 1 % 0 := hmod
        rwa [Nat.mod_zero, Nat.mod_zero] at h2
      exact hprime.ne_one hp1
    have hBnn : 0 ≤ B := by
      have hsum := hBV (fun _ => 1) (fun q => Nat.coprime_one_left q)
      exact le_trans (Finset.sum_nonneg (fun q _ => abs_nonneg _)) hsum
    rw [hcount, Nat.totient_zero]
    simp only [Nat.cast_zero, div_zero, sub_zero, abs_zero]
    exact hBnn
  · -- Positive modulus: the argmax bridge, with range membership.
    exact maxCoprimeErr_le_of_sum_bound
      (M := fun Y L => li (Y : ℝ) / (Nat.totient L : ℝ)) (Y := Y)
      (S := (Finset.range ⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊).filter
        (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ) ^ (1 / 2 - η))) (B := B)
      hBV (mem_bvRange_of_le_sq hLpos hLR hlevel) hr

/-! ### The error-bound function: BV bound at controlled heights, crude elsewhere -/

/-- The error bound used by the combined corollary: the BV bound
    `C * Y' * log(Y')^(-A')` at heights where the BV input applies
    (`2 ≤ Y'` and the level constraint), and the crude bound
    `(Y'+1) + |li(Y')|` elsewhere. The crude branch is only ever a
    hypothesis-feeder: the conclusion evaluates the bound solely at
    the interval endpoints, where the controlled branch holds. -/
noncomputable def bvErrBoundFun (R : ℕ) (η A' C : ℝ) (li : ℝ → ℝ) (Y' : ℕ) : ℝ := by
  classical
  exact if 2 ≤ Y' ∧ (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) then
    C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A'))
  else ((Y' : ℝ) + 1 + |li (Y' : ℝ)|)

/-- The controlled branch of `bvErrBoundFun`. -/
theorem bvErrBoundFun_eq_of {R : ℕ} {η A' C : ℝ} {li : ℝ → ℝ} {Y' : ℕ}
    (hc : 2 ≤ Y' ∧ (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)) :
    bvErrBoundFun R η A' C li Y' = C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')) := by
  unfold bvErrBoundFun
  rw [if_pos hc]

/-- The crude branch of `bvErrBoundFun`. -/
theorem bvErrBoundFun_eq_of_not {R : ℕ} {η A' C : ℝ} {li : ℝ → ℝ} {Y' : ℕ}
    (hc : ¬ (2 ≤ Y' ∧ (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))) :
    bvErrBoundFun R η A' C li Y' = (Y' : ℝ) + 1 + |li (Y' : ℝ)| := by
  unfold bvErrBoundFun
  rw [if_neg hc]

/-! ### Combined corollary: the second moment with a BV-controlled error -/

/-- Combined corollary: under BV-style sum bounds at every controlled
    height (the shape the platform BV record supplies, after the
    floor conversion `⌊(Y':ℝ)⌋₊ = Y'` identifying
    `primeCountingAP` with `primeCountAP`), with `C ≥ 0`, and with
    the level constraint and `2 ≤ Y'` holding at every interval
    endpoint `y + h i` and `x + h i`, the second moment equals the BV
    main term up to λ-mass times (R² times the summed endpoint BV
    bounds, plus one per coordinate for the bad pairs). -/
theorem secondMoment_bvErrBound_of_bvSumBound {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y)
    {η A' C : ℝ} (hC : 0 ≤ C) (li : ℝ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - li (Y' : ℝ) / (Nat.totient q : ℝ))
          ≤ C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')))
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (secondMoment k h R lam x y
        - bvMainTerm k h R lam (fun Y L => li (Y : ℝ) / (Nat.totient L : ℝ)) x y)
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
        * ((R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + C * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ)) := by
  -- Nonnegativity of the error-bound function at every height.
  have hE : ∀ Y', 0 ≤ bvErrBoundFun R η A' C li Y' := by
    intro Y'
    by_cases hc : 2 ≤ Y' ∧ (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)
    · rw [bvErrBoundFun_eq_of hc]
      have h2 : (2 : ℝ) ≤ (Y' : ℝ) := by exact_mod_cast hc.1
      have hY'pos : (0 : ℝ) < (Y' : ℝ) := by linarith
      have hlog : 0 < Real.log (Y' : ℝ) := Real.log_pos (by linarith)
      have hrpow : 0 < Real.log (Y' : ℝ) ^ (-A') := Real.rpow_pos_of_pos hlog _
      exact mul_nonneg hC (le_of_lt (mul_pos hY'pos hrpow))
    · rw [bvErrBoundFun_eq_of_not hc]
      have h1 : (0 : ℝ) ≤ (Y' : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ |li (Y' : ℝ)| := abs_nonneg _
      linarith
  -- The pointwise bound at every height: BV-controlled where the
  -- input applies, crude elsewhere.
  have hErr : ∀ Y' L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs ((primeCountAP Y' L r : ℝ) - li (Y' : ℝ) / (Nat.totient L : ℝ))
        ≤ bvErrBoundFun R η A' C li Y' := by
    intro Y' L r hLR hr
    by_cases hc : 2 ≤ Y' ∧ (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)
    · rw [bvErrBoundFun_eq_of hc]
      exact hErr_of_bvSumBound (hBV Y' hc.1 hc.2) hc.2 L r hLR hr
    · rw [bvErrBoundFun_eq_of_not hc]
      have hcard : (primeCountAP Y' L r : ℝ) ≤ (Y' : ℝ) + 1 := by
        have hle : primeCountAP Y' L r ≤ Y' + 1 := by
          unfold primeCountAP
          calc ((Finset.range (Y' + 1)).filter
                (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card
              ≤ (Finset.range (Y' + 1)).card := Finset.card_filter_le _ _
            _ = Y' + 1 := Finset.card_range _
        calc (primeCountAP Y' L r : ℝ) ≤ ((Y' + 1 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (Y' : ℝ) + 1 := by push_cast; ring
      have hmodel : abs (li (Y' : ℝ) / (Nat.totient L : ℝ)) ≤ |li (Y' : ℝ)| := by
        by_cases hL0 : L = 0
        · subst hL0
          rw [Nat.totient_zero]
          simp only [Nat.cast_zero, div_zero, abs_zero]
          exact abs_nonneg _
        · have hφ : (1 : ℝ) ≤ (Nat.totient L : ℝ) := by
            have hpos : 0 < Nat.totient L :=
              Nat.totient_pos.mpr (Nat.pos_of_ne_zero hL0)
            exact_mod_cast (show 1 ≤ Nat.totient L from hpos)
          have hφnn : (0 : ℝ) ≤ (Nat.totient L : ℝ) := Nat.cast_nonneg _
          rw [abs_div, abs_of_nonneg hφnn]
          exact div_le_self (abs_nonneg _) hφ
      calc abs ((primeCountAP Y' L r : ℝ) - li (Y' : ℝ) / (Nat.totient L : ℝ))
          ≤ abs (primeCountAP Y' L r : ℝ)
            + abs (li (Y' : ℝ) / (Nat.totient L : ℝ)) := abs_sub _ _
        _ = (primeCountAP Y' L r : ℝ)
            + abs (li (Y' : ℝ) / (Nat.totient L : ℝ)) := by
            rw [abs_of_nonneg (Nat.cast_nonneg (primeCountAP Y' L r))]
        _ ≤ ((Y' : ℝ) + 1) + |li (Y' : ℝ)| := add_le_add hcard hmodel
  -- Apply the error-control corollary, then evaluate the bound at
  -- the endpoints, where the controlled branch holds.
  have hmain := secondMoment_bvErrBound k h R lam
    (fun Y L => li (Y : ℝ) / (Nat.totient L : ℝ)) (bvErrBoundFun R η A' C li)
    hxy hE hErr
  have hsum : (∑ i, (bvErrBoundFun R η A' C li (y + h i)
        + bvErrBoundFun R η A' C li (x + h i)))
      = ∑ i, (C * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
        + C * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A'))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [bvErrBoundFun_eq_of ⟨(hY2 i).1, (hlevel i).1⟩,
      bvErrBoundFun_eq_of ⟨(hY2 i).2, (hlevel i).2⟩]
  rw [hsum] at hmain
  exact hmain


/-! ### Max coprime-residue error at one height and modulus -/

/-- The maximum coprime-residue model error at height `Y` and modulus
    `L`: the finite max of |π(Y; L, r) − M Y L| over coprime residues
    `r < L`, or 0 when there are none (which happens only for L = 0).
    This is the quantity the grouped bound needs: unlike the coprime
    SUM, it does not cost a factor L. -/
noncomputable def maxCoprimeErr (M : ℕ → ℕ → ℝ) (Y L : ℕ) : ℝ := by
  classical
  exact if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h
    else 0

/-- For positive `L`, the coprime residues mod `L` are nonempty: 0
    works for L = 1, and 1 works for L > 1. -/
theorem coprimeResidues_nonempty {L : ℕ} (hLpos : 0 < L) :
    ((Finset.range L).filter (fun r => Nat.Coprime r L)).Nonempty := by
  by_cases hL1 : L = 1
  · subst hL1
    exact ⟨0, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, by decide⟩⟩
  · exact ⟨1, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.coprime_one_left L⟩⟩

/-- The max coprime error is nonnegative (it is a max of absolute
    values, or 0 in the degenerate case). -/
theorem maxCoprimeErr_nonneg (M : ℕ → ℕ → ℝ) (Y L : ℕ) :
    0 ≤ maxCoprimeErr M Y L := by
  classical
  unfold maxCoprimeErr
  by_cases himg : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty
  · rw [dif_pos himg]
    obtain ⟨r₀, _, hr₀⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
    rw [← hr₀]
    exact abs_nonneg _
  · rw [dif_neg himg]

/-- A coprime-residue error is at most the max: the residue mod `L`
    is itself coprime (gcd is preserved under mod), so it is a term
    of the finite max. -/
theorem le_maxCoprimeErr (M : ℕ → ℕ → ℝ) (Y : ℕ) {L : ℕ} (hLpos : 0 < L)
    {r : ℕ} (hr : Nat.Coprime r L) :
    abs ((primeCountAP Y L r : ℝ) - M Y L) ≤ maxCoprimeErr M Y L := by
  classical
  have hmem : r % L ∈ (Finset.range L).filter (fun r => Nat.Coprime r L) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hLpos, ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one] at hr ⊢
    rw [← Nat.gcd_rec L r, Nat.gcd_comm L r]
    exact hr
  have himg := (coprimeResidues_nonempty hLpos).image
    (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))
  have hle : abs ((primeCountAP Y L (r % L) : ℝ) - M Y L) ≤
      (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
        (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' himg := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨r % L, hmem, rfl⟩
  unfold maxCoprimeErr
  rw [dif_pos himg, ← primeCountAP_eq_of_modEq (Nat.mod_modEq r L)]
  exact hle

/-- The max at a modulus in range is at most the BV sum bound: the
    max is attained at some coprime residue, and the existing argmax
    bridge bounds that residue's error by the sum. -/
theorem maxCoprimeErr_le_of_sum_bound_at (M : ℕ → ℕ → ℝ) (Y : ℕ) (S : Finset ℕ) (B : ℝ)
    (hB : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ S, abs ((primeCountAP Y q (v q) : ℝ) - M Y q) ≤ B)
    {L : ℕ} (hL : L ∈ S) (hLpos : 0 < L) :
    maxCoprimeErr M Y L ≤ B := by
  classical
  have himg := (coprimeResidues_nonempty hLpos).image
    (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))
  unfold maxCoprimeErr
  rw [dif_pos himg]
  obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
  rw [Finset.mem_filter] at hr₀mem
  rw [← hr₀eq]
  exact maxCoprimeErr_le_of_sum_bound M Y S B hB hL hr₀mem.2

/-- The sum of the maxes over any range is at most the BV sum bound:
    build a choice function from the attained maxima (0 is coprime
    to nothing, so the L = 0 case uses residue 1 and the bound
    0 ≤ error), then apply the sum hypothesis to it. No analysis. -/
theorem sum_maxCoprimeErr_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y : ℕ) (S : Finset ℕ) (B : ℝ)
    (hB : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ S, abs ((primeCountAP Y q (v q) : ℝ) - M Y q) ≤ B) :
    ∑ L ∈ S, maxCoprimeErr M Y L ≤ B := by
  classical
  have hex : ∀ q : ℕ, ∃ r : ℕ, Nat.Coprime r q ∧
      maxCoprimeErr M Y q ≤ abs ((primeCountAP Y q r : ℝ) - M Y q) := by
    intro q
    by_cases hq0 : q = 0
    · subst hq0
      refine ⟨1, Nat.coprime_one_left 0, ?_⟩
      have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
          (fun r => abs ((primeCountAP Y 0 r : ℝ) - M Y 0)))).Nonempty := by
        rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
        exact Finset.not_nonempty_empty
      unfold maxCoprimeErr
      rw [dif_neg hne0]
      exact abs_nonneg _
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have himg := (coprimeResidues_nonempty hqpos).image
        (fun r => abs ((primeCountAP Y q r : ℝ) - M Y q))
      obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
      refine ⟨r₀, (Finset.mem_filter.mp hr₀mem).2, ?_⟩
      unfold maxCoprimeErr
      rw [dif_pos himg, ← hr₀eq]
  choose v hvCop hvMax using hex
  calc ∑ L ∈ S, maxCoprimeErr M Y L
      ≤ ∑ L ∈ S, abs ((primeCountAP Y L (v L) : ℝ) - M Y L) :=
        Finset.sum_le_sum (fun L _ => hvMax L)
    _ ≤ B := hB v hvCop

/-! ### Tight single-residue identity: no coprime sum, no R² -/

/-- Error summand for one triple, tight version: for a good pair, the
    two WITNESS errors at the interval endpoints (the witness is
    supplied by the selector `wit`, so no choice appears in the
    statement); 1 for a bad pair, exactly as in the coprime version.
    Compare `bvErrSummandCoprime`, which sums over ALL coprime
    residues — this is the step that cost the factor L. -/
noncomputable def tightErrSummand (M : ℕ → ℕ → ℝ) {k : ℕ} (h d e : Fin k → ℕ)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ) (i : Fin k) (x y : ℕ) : ℝ := by
  classical
  exact if goodPair h d e i then
    abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
        - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
        - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    else 1

/-- The tight error bound for the second moment: `|λ_d λ_e|` times
    the per-triple witness-error summand, summed over support pairs
    and coordinates. -/
noncomputable def tightErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (x y : ℕ)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    abs (lam d * lam e) * (∑ i, tightErrSummand M h d e wit i x y)

/-- Tight identity: the linear second moment `S₂` equals the BV main
    term up to the WITNESS-error bound. Same proof shape as
    `secondMoment_bvMainTerm_coprime`, but the per-triple step uses
    `jointPrimeCount_approx` directly — no `single_le_sum` over the
    coprime residues, hence no factor L and no R² anywhere. The
    witness selector is an explicit parameter: the theorem holds for
    ANY selector satisfying `hwit`, so the statement involves no
    choice. -/
theorem secondMoment_tightErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ tightErrBound k h R lam M x y wit := by
  classical
  have per_i : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R, ∀ t,
      abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
        - bvMainSummand M h d e t x y) ≤ tightErrSummand M h d e wit t x y := by
    intro d hd e he t
    have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
    have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
    have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
      intro j
      apply Nat.lcm_ne_zero
      · have hj1 := hd1 j
        omega
      · have hj2 := he1 j
        omega
    by_cases hgood : goodPair h d e t
    · unfold bvMainSummand tightErrSummand
      rw [if_pos hgood, if_pos hgood]
      exact jointPrimeCount_approx M t (wit d e t) (hwit d e t hgood).1 hxy
    · by_cases hcomp : (∀ i' j', h i' ≡ h j' [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))])
      · obtain ⟨w₀, hw₀⟩ := exists_dvd_of_compatible (m := fun j => Nat.lcm (d j) (e j)) hmne hcomp
        have hgcd : Nat.gcd (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ≠ 1 := by
          intro hg
          exact hgood ⟨w₀, hw₀, Nat.coprime_iff_gcd_eq_one.mpr hg⟩
        have hncop : ¬ Nat.Coprime (w₀ + h t) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
          fun hc => hgcd (Nat.coprime_iff_gcd_eq_one.mp hc)
        have hle := jointPrimeCount_le_one_of_not_coprime (x := x) (y := y) t w₀ hw₀ hncop
        unfold bvMainSummand tightErrSummand
        rw [if_neg hgood, if_neg hgood]
        rw [sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hle
      · push_neg at hcomp
        obtain ⟨i₀, j₀, hij⟩ := hcomp
        have hzero := primeCount_eq_zero_of_incompatible (x := x) (y := y) t ⟨i₀, j₀, hij⟩
        unfold bvMainSummand tightErrSummand
        rw [if_neg hgood, if_neg hgood, hzero]
        simp
  have per_pair : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, tightErrSummand M h d e wit t x y) := by
    intro d hd e he
    have heq : lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)
        = lam d * lam e * (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [heq, abs_mul]
    calc abs (lam d * lam e) * abs (∑ t, (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y))
        ≤ abs (lam d * lam e) * (∑ t, abs (((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ)
          - bvMainSummand M h d e t x y)) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ abs (lam d * lam e) * (∑ t, tightErrSummand M h d e wit t x y) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => per_i d hd e he t)) (abs_nonneg _)
  rw [secondMoment_eq]
  unfold bvMainTerm tightErrBound
  simp only [← Finset.sum_sub_distrib]
  calc abs (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)))
      ≤ ∑ d ∈ tupleSupport k R, abs (∑ e ∈ tupleSupport k R,
        (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e * (∑ t, ((Finset.filter (fun n => ((∀ j, d j ∣ n + h j) ∧ ∀ j, e j ∣ n + h j) ∧ Nat.Prime (n + h t)) (Finset.Ioc x y)).card : ℝ))
        - lam d * lam e * (∑ t, bvMainSummand M h d e t x y)) :=
        Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * (∑ t, tightErrSummand M h d e wit t x y) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => per_pair d hd e he))

/-! ### Fiber weights and the grouped bound -/

/-- Fiber weight at coordinate `i` and modulus `L`: the total
    `|λ_d λ_e|` over support pairs `(d, e)` whose combined modulus
    is `L` and which are good at `i`. This is the weight the BV sum
    must absorb — the whole point of the weighted combination is
    that these weights, not the bare mass Λ, multiply the BV sums. -/
noncomputable def fiberWeight {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) (L : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
      (fun p => goodPair h p.1 p.2 i ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
    abs (lam p.1 * lam p.2)

/-- Fiber weights are nonnegative (sums of absolute values). -/
theorem fiberWeight_nonneg {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) (L : ℕ) :
    0 ≤ fiberWeight h R lam i L := by
  unfold fiberWeight
  exact Finset.sum_nonneg (fun p _ => abs_nonneg _)

/-- The trivial fiber bound: a fiber is a subset of the product, so
    its weight is at most the total mass Λ. This is what turns the
    conditional corollary into the Y^{2θ}-gap bound below — and it
    is also exactly why that bound does not separate: Λ is too big. -/
theorem fiberWeight_le_mass {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) (L : ℕ) :
    fiberWeight h R lam i L
      ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e) := by
  classical
  unfold fiberWeight
  calc (∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
        abs (lam p.1 * lam p.2))
      ≤ ∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R, abs (lam p.1 * lam p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => abs_nonneg _)
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e) :=
        Finset.sum_product' _ _ (fun d e => abs (lam d * lam e))

/-- Grouped bound: the second-moment error, with the good-pair part
    grouped by combined modulus L and weighted by the fiber weights,
    plus the bad-pair term Λ·k. The modulus range is R²+1 because
    every support pair has L ≤ R² (`lcm_le_sq_of_mem_support`). -/
theorem secondMoment_groupedErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
  classical
  have hif : ∀ (b : Prop) [Decidable b] (a : ℝ),
      (if b then a else 1) = (if b then a else 0) + (if b then 0 else 1) := by
    intro b _ a
    by_cases hb : b <;> simp [hb]
  have hsplit : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (∑ i, tightErrSummand M h d e wit i x y)
        = (∑ i, if goodPair h d e i then
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              else 0)
          + (∑ i, if goodPair h d e i then 0 else 1) := by
    intro d _ e _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold tightErrSummand
    exact hif _ _
  have hswap : ∀ g : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℝ,
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lam d * lam e) * (∑ i, g d e i))
        = ∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lam d * lam e) * g d e i := by
    intro g
    simp only [Finset.mul_sum]
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, ∑ i, abs (lam d * lam e) * g d e i)
        = ∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R, ∑ i, abs (lam p.1 * lam p.2) * g p.1 p.2 i :=
          (Finset.sum_product' _ _ (fun d e => ∑ i, abs (lam d * lam e) * g d e i)).symm
      _ = ∑ i, ∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R, abs (lam p.1 * lam p.2) * g p.1 p.2 i :=
          Finset.sum_comm
      _ = ∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e) * g d e i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_product' _ _ (fun d e => abs (lam d * lam e) * g d e i)
  have hbad : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1))
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1))
        ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e) * (k : ℝ) := by
          apply Finset.sum_le_sum
          intro d _
          apply Finset.sum_le_sum
          intro e _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc (∑ i, if goodPair h d e i then 0 else 1)
              ≤ ∑ _i : Fin k, 1 := by
                apply Finset.sum_le_sum
                intro i _
                by_cases hg : goodPair h d e i <;> simp [hg]
            _ = (k : ℝ) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ = (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
          simp only [← Finset.sum_mul]
  have hgood_i : ∀ i,
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lam d * lam e) * (if goodPair h d e i then
            (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
            else 0))
        ≤ ∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L) := by
    intro i
    have hmaps : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter (fun p => goodPair h p.1 p.2 i),
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) ∈ Finset.range (R ^ 2 + 1) := by
      intro p hp
      rw [Finset.mem_range]
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      have hle := lcm_le_sq_of_mem_support hp1 hp2
      omega
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (if goodPair h d e i then
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              else 0))
        = ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter (fun p => goodPair h p.1 p.2 i),
            abs (lam p.1 * lam p.2) *
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))) := by
          rw [← Finset.sum_product', Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p _
          by_cases hg : goodPair h p.1 p.2 i <;> simp [hg]
      _ = ∑ L ∈ Finset.range (R ^ 2 + 1),
            ∑ p ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter (fun p => goodPair h p.1 p.2 i)).filter
              (fun p => Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
            abs (lam p.1 * lam p.2) *
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))) :=
          by rw [Finset.sum_fiberwise_of_maps_to hmaps]
      _ ≤ ∑ L ∈ Finset.range (R ^ 2 + 1),
            fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L) := by
          apply Finset.sum_le_sum
          intro L _
          rw [Finset.filter_filter]
          calc (∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
                (fun p => goodPair h p.1 p.2 i ∧
                  Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
              abs (lam p.1 * lam p.2) *
                (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                    - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))
                  + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                    - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))))
              ≤ ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
                  (fun p => goodPair h p.1 p.2 i ∧
                    Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
                abs (lam p.1 * lam p.2) * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L) := by
                apply Finset.sum_le_sum
                intro p hp
                have hpgood : goodPair h p.1 p.2 i := (Finset.mem_filter.mp hp).2.1
                have hpL : Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L :=
                  (Finset.mem_filter.mp hp).2.2
                have hp1 : p.1 ∈ tupleSupport k R :=
                  (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
                have hp2 : p.2 ∈ tupleSupport k R :=
                  (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
                have hLpos : 0 < L := by
                  rw [← hpL]
                  exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun j _ => by
                    apply Nat.lcm_ne_zero
                    · have h1j := (mem_tupleSupport.mp hp1).1 j
                      omega
                    · have h2j := (mem_tupleSupport.mp hp2).1 j
                      omega))
                have hcop : Nat.Coprime (wit p.1 p.2 i + h i) L := by
                  rw [← hpL]
                  exact (hwit p.1 p.2 i hpgood).2
                have hw1 : abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                      - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))
                    ≤ maxCoprimeErr M (y + h i) L := by
                  rw [hpL]
                  exact le_maxCoprimeErr M _ hLpos hcop
                have hw2 : abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))) (wit p.1 p.2 i + h i) : ℝ)
                      - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j))))
                    ≤ maxCoprimeErr M (x + h i) L := by
                  rw [hpL]
                  exact le_maxCoprimeErr M _ hLpos hcop
                exact mul_le_mul_of_nonneg_left (add_le_add hw1 hw2) (abs_nonneg _)
            _ = fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L) := by
                unfold fiberWeight
                rw [Finset.sum_mul]
  have hdecomp : tightErrBound k h R lam M x y wit
      ≤ (∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lam d * lam e) * (if goodPair h d e i then
            (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
            else 0))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
    unfold tightErrBound
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (∑ i, tightErrSummand M h d e wit i x y))
        = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            (abs (lam d * lam e) * (∑ i, if goodPair h d e i then
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              else 0)
            + abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1)) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [hsplit d hd e he, mul_add]
      _ = (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (∑ i, if goodPair h d e i then
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              else 0))
          + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1)) := by
          calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
                (abs (lam d * lam e) * (∑ i, if goodPair h d e i then
                  (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                      - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                    + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                      - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                  else 0)
                + abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1)))
              = ∑ d ∈ tupleSupport k R,
                  ((∑ e ∈ tupleSupport k R, abs (lam d * lam e) * (∑ i, if goodPair h d e i then
                    (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                        - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                      + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                        - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                    else 0))
                  + (∑ e ∈ tupleSupport k R, abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1))) :=
                Finset.sum_congr rfl (fun d _ => Finset.sum_add_distrib)
            _ = (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
                  abs (lam d * lam e) * (∑ i, if goodPair h d e i then
                    (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                        - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                      + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                        - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                    else 0))
                + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
                  abs (lam d * lam e) * (∑ i, if goodPair h d e i then 0 else 1)) :=
                Finset.sum_add_distrib
      _ ≤ (∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lam d * lam e) * (if goodPair h d e i then
              (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
                + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                  - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              else 0))
          + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
          apply add_le_add _ hbad
          exact le_of_eq (hswap _)
  calc abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ tightErrBound k h R lam M x y wit :=
        secondMoment_tightErrBound k h R lam M hxy wit hwit
    _ ≤ (∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lam d * lam e) * (if goodPair h d e i then
            (abs ((primeCountAP (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              + abs ((primeCountAP (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) (wit d e i + h i) : ℝ)
                - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
            else 0))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) :=
        hdecomp
    _ ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
        have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hgood_i i)
        linarith

/-! ### Conditional separation corollary, and the mass instance -/

/-- Conditional separation: under a platform-shaped BV sum hypothesis
    at every endpoint height (with the level constraint and `2 ≤ Y'`
    at the endpoints), and a uniform fiber bound `fiberWeight ≤ Wbar`,
    the second-moment error is at most Wbar times the BV sums plus
    the bad-pair term. The content is in the hypotheses: with
    Wbar = Λ this recovers a bound R² better than the proved max-form
    bound, and separation needs Wbar polylog — which is exactly the
    open fiber/divisor-weighted question, NOT claimed here. -/
theorem secondMoment_weightedBV_bound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i)
    (Wbar : ℝ) (hWnn : 0 ≤ Wbar) (hW : ∀ i L, fiberWeight h R lam i L ≤ Wbar) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ Wbar * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
  classical
  have hgrouped := secondMoment_groupedErrBound k h R lam M hxy wit hwit
  have hsumMax : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L) ≤ B Y' := by
    intro Y' h2 hlev
    have h0 : maxCoprimeErr M Y' 0 = 0 := by
      have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
          (fun r => abs ((primeCountAP Y' 0 r : ℝ) - M Y' 0)))).Nonempty := by
        rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
        exact Finset.not_nonempty_empty
      unfold maxCoprimeErr
      rw [dif_neg hne0]
    have hsplit : (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L)
        = ∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => 1 ≤ L), maxCoprimeErr M Y' L := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (R ^ 2 + 1)) (fun L => 1 ≤ L)
        (fun L => maxCoprimeErr M Y' L)]
      have hnot : (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => ¬ 1 ≤ L),
          maxCoprimeErr M Y' L) = 0 := by
        apply Finset.sum_eq_zero
        intro L hL
        rw [Finset.mem_filter] at hL
        have hL0 : L = 0 := by omega
        rw [hL0, h0]
      rw [hnot, add_zero]
    rw [hsplit]
    calc (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => 1 ≤ L), maxCoprimeErr M Y' L)
        ≤ ∑ L ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
            (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)), maxCoprimeErr M Y' L := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro L hL
            rw [Finset.mem_filter, Finset.mem_range] at hL
            exact mem_bvRange_of_le_sq hL.2 (by omega) hlev
          · intro L _ _
            exact maxCoprimeErr_nonneg _ _ _
      _ ≤ B Y' := sum_maxCoprimeErr_le_of_sum_bound M Y' _ _ (hBV Y' h2 hlev)
  have hper : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
        fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
      ≤ Wbar * (B (y + h i) + B (x + h i)) := by
    intro i
    calc (∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
        ≤ ∑ L ∈ Finset.range (R ^ 2 + 1),
          Wbar * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L) := by
          apply Finset.sum_le_sum
          intro L _
          exact mul_le_mul_of_nonneg_right (hW i L)
            (add_nonneg (maxCoprimeErr_nonneg _ _ _) (maxCoprimeErr_nonneg _ _ _))
      _ = Wbar * (∑ L ∈ Finset.range (R ^ 2 + 1),
          (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L)) := by
          rw [Finset.mul_sum]
      _ = Wbar * ((∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M (y + h i) L)
          + (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M (x + h i) L)) := by
          rw [Finset.sum_add_distrib]
      _ ≤ Wbar * (B (y + h i) + B (x + h i)) := by
          apply mul_le_mul_of_nonneg_left _ hWnn
          exact add_le_add (hsumMax _ (hY2 i).1 (hlevel i).1) (hsumMax _ (hY2 i).2 (hlevel i).2)
  calc abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R lam i L * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) :=
        hgrouped
    _ ≤ (∑ i, Wbar * (B (y + h i) + B (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
        have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hper i)
        linarith
    _ = Wbar * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) := by
        rw [← Finset.mul_sum]

/-- Mass instance: with Wbar = Λ (the trivial fiber bound), the error
    is at most Λ times the BV sums plus Λ·k — a full R² better than
    the proved max-form bound Λ·(R²·∑E + k), i.e. the Y^{2θ}-gap
    bound, now proved rather than merely analyzed. Separation still
    needs a better-than-Λ fiber bound, which is open (see header). -/
theorem secondMoment_weightedBV_bound_mass (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (secondMoment k h R lam x y - bvMainTerm k h R lam M x y)
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
          * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e)) * (k : ℝ) :=
  secondMoment_weightedBV_bound k h R lam M hxy wit hwit B hBV hlevel hY2
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, abs (lam d * lam e))
    (Finset.sum_nonneg (fun _d _ => Finset.sum_nonneg (fun _e _ => abs_nonneg _)))
    (fun i L => fiberWeight_le_mass h R lam i L)


/-! ### The Selberg weight -/

/-- Classical GPY/Selberg tuple weight of degree `deg`: the Möbius
    function of the total product times the polynomial cutoff
    `(1 - log D / log R)^deg`, supported where `D ≤ R`. -/
noncomputable def lamSelberg (k : ℕ) (R : ℕ) (deg : ℕ) (d : Fin k → ℕ) : ℝ :=
  if ∏ i, d i ≤ R then
    (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
      * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
  else 0

/-- On the support, the weight is the μ-times-polynomial form. -/
theorem lamSelberg_eq_of_mem_support {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d
      = (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg := by
  unfold lamSelberg
  rw [if_pos (mem_tupleSupport.mp hd).2.2]

/-- The weight vanishes off squarefree products: Möbius kills them. -/
theorem lamSelberg_eq_zero_of_not_squarefree {k R deg : ℕ} {d : Fin k → ℕ}
    (h : ¬ Squarefree (∏ i, d i)) : lamSelberg k R deg d = 0 := by
  unfold lamSelberg
  by_cases hle : ∏ i, d i ≤ R
  · rw [if_pos hle]
    have hmu : (ArithmeticFunction.moebius (∏ i, d i) : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
    rw [hmu, zero_mul]
  · rw [if_neg hle]

/-- On the support, the weight is bounded by 1 in absolute value:
    `|μ| ≤ 1` and the cutoff factor lies in `[0, 1]` for `2 ≤ R`. -/
theorem abs_lamSelberg_le_one {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) (hR : 2 ≤ R) :
    |lamSelberg k R deg d| ≤ 1 := by
  obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hd
  have hD1 : 1 ≤ ∏ i, d i := Finset.one_le_prod' (fun i _ => h1 i)
  have hDpos : (0 : ℝ) < (∏ i, d i : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hD1)
  have hlogR : (0 : ℝ) < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogD_nn : (0 : ℝ) ≤ Real.log (∏ i, d i : ℕ) :=
    Real.log_nonneg (by exact_mod_cast hD1)
  have hlogD_le : Real.log (∏ i, d i : ℕ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log hDpos (by exact_mod_cast h3)
  have hfrac_nn : (0 : ℝ) ≤ Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ) :=
    div_nonneg hlogD_nn hlogR.le
  have hfrac_le : Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ) ≤ 1 :=
    (div_le_one hlogR).mpr hlogD_le
  have hfac_nn : (0 : ℝ) ≤ 1 - Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ) := by
    linarith
  have hfac_le : 1 - Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ) ≤ 1 := by
    linarith
  have hpow_nn : (0 : ℝ) ≤ (1 - Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ)) ^ deg :=
    pow_nonneg hfac_nn _
  have hpow_le : (1 - Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ)) ^ deg ≤ 1 :=
    pow_le_one₀ hfac_nn hfac_le
  have hmu : |(ArithmeticFunction.moebius (∏ i, d i) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [lamSelberg_eq_of_mem_support hd, abs_mul, abs_of_nonneg hpow_nn]
  calc |(ArithmeticFunction.moebius (∏ i, d i) : ℝ)|
        * (1 - Real.log (∏ i, d i : ℕ) / Real.log (R : ℝ)) ^ deg
      ≤ 1 * 1 := mul_le_mul hmu hpow_le hpow_nn zero_le_one
    _ = 1 := one_mul 1

/-- The weight vanishes when the total product equals the level
    (for `deg ≥ 1`): the cutoff factor is `1 - 1 = 0` there. -/
theorem lamSelberg_eq_zero_of_prod_eq {k R deg : ℕ} {d : Fin k → ℕ}
    (hR : 2 ≤ R) (hdeg : 1 ≤ deg) (hprod : ∏ i, d i = R) :
    lamSelberg k R deg d = 0 := by
  have hle : ∏ i, d i ≤ R := hprod.le
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < R by omega)))
  unfold lamSelberg
  rw [if_pos hle, hprod, div_self hlogR, sub_self,
    zero_pow (show deg ≠ 0 by omega), mul_zero]

/-! ### The divisor-count function and the fiberwise identity -/

/-- Number of ordered factorizations of `D` into `k` positive factors:
    the `k`-fold divisor function `τ_k(D)` in the form the sums need.
    (Each factor is at most `D` automatically when the product is `D`
    and all factors are positive, so `Icc 1 D` is the right range.) -/
def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

/-- The fiber of the support over a product `D ≤ R` has card
    `τ_k(D)`: a support tuple with product `D` has all entries at
    most `D` (each entry is at most the product, since the other
    factors are at least 1), and conversely entries at most `D` with
    product `D` are automatically at most `R` and in the support. -/
theorem filter_tupleSupport_prod_eq {k R D : ℕ} (_hD1 : 1 ≤ D) (hDR : D ≤ R) :
    ((tupleSupport k R).filter (fun d => ∏ i, d i = D)).card
      = tupleProdCount k D := by
  have hset : (tupleSupport k R).filter (fun d => ∏ i, d i = D)
      = (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D) := by
    ext d
    simp only [Finset.mem_filter, mem_tupleSupport, Fintype.mem_piFinset,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -, -⟩, hprod⟩
      refine ⟨fun i => ⟨h1 i, ?_⟩, hprod⟩
      have hle : d i ≤ ∏ j, d j :=
        Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
      rw [hprod] at hle
      exact hle
    · rintro ⟨h1D, hprod⟩
      refine ⟨⟨fun i => (h1D i).1, fun i => le_trans (h1D i).2 hDR, ?_⟩, hprod⟩
      rw [hprod]
      exact hDR
  rw [hset, tupleProdCount]

/-- Exact fiberwise identity: the `ℓ¹` mass of the Selberg weight over
    the support equals the divisor-weighted sum over products. -/
theorem sum_abs_lamSelberg_eq {k R deg : ℕ} :
    ∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|
      = ∑ D ∈ Finset.Icc 1 R,
        (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
  have hmaps : ∀ d ∈ tupleSupport k R, ∏ i, d i ∈ Finset.Icc 1 R := by
    intro d hd
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hd
    rw [Finset.mem_Icc]
    exact ⟨Finset.one_le_prod' (fun i _ => h1 i), h3⟩
  have hinner : ∀ D ∈ Finset.Icc 1 R,
      (∑ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
        |lamSelberg k R deg d|)
        = (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    have hterm : ∀ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
        |lamSelberg k R deg d|
          = |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
      intro d hd
      rw [Finset.mem_filter] at hd
      rw [lamSelberg_eq_of_mem_support hd.1, hd.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      filter_tupleSupport_prod_eq hD.1 hD.2]
  calc ∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|
      = ∑ D ∈ Finset.Icc 1 R,
          ∑ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
            |lamSelberg k R deg d| :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ D ∈ Finset.Icc 1 R,
          (tupleProdCount k D : ℝ)
            * |(ArithmeticFunction.moebius D : ℝ)
              * (1 - Real.log D / Real.log R) ^ deg| :=
        Finset.sum_congr rfl hinner

/-! ### The τ-weighted λ-mass -/

/-- The λ-mass factors as the square of the `ℓ¹` mass. -/
theorem lambdaMass_eq_sq {k R deg : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|) ^ 2 := by
  have hstep : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|)
        * (∑ e ∈ tupleSupport k R, |lamSelberg k R deg e|) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    rw [abs_mul]
  rw [hstep, pow_two]

/-- The τ-weighted λ-mass identity: `Λ` equals the square of the
    divisor-weighted sum. This is the sharp form of the mass bound:
    the squarefree restriction (via `μ`) and the polynomial decay
    (via the cutoff factor) stay visible, instead of being thrown
    away into the crude `|support|²` bound. -/
theorem lambdaMass_lamSelberg_eq {k R deg : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ D ∈ Finset.Icc 1 R,
        (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg|) ^ 2 := by
  rw [lambdaMass_eq_sq, sum_abs_lamSelberg_eq]

/-- For comparison, the crude bound: `Λ ≤ |support|²`, obtained by
    throwing away the μ-factor and the cutoff decay (`|λ| ≤ 1`). -/
theorem lambdaMass_lamSelberg_le {k R deg : ℕ} (hR : 2 ≤ R) :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      |lamSelberg k R deg d * lamSelberg k R deg e|)
      ≤ ((tupleSupport k R).card : ℝ) ^ 2 := by
  have h1 : (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|)
      ≤ ((tupleSupport k R).card : ℝ) := by
    calc (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|)
        ≤ ∑ _d ∈ tupleSupport k R, (1 : ℝ) :=
          Finset.sum_le_sum (fun d hd => abs_lamSelberg_le_one hd hR)
      _ = ((tupleSupport k R).card : ℝ) := by simp
  rw [lambdaMass_eq_sq]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => abs_nonneg _)) h1 2

/-! ### Multiplicativity of the μ-part (and its limit) -/

/-- The Möbius part of the weight is multiplicative: this is the one
    ingredient of the singular-series factorization that is already
    available. The full weight is NOT multiplicative — the cutoff
    `(1 - log(D₁D₂)/log R)^deg` does not factor over coprime
    products — and that non-factorization is precisely why the
    singular-series evaluation needs the smoothed-sum analysis
    listed as remaining work, rather than a pure Euler product. -/
theorem moebius_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    (ArithmeticFunction.moebius (m * n) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ)
        * (ArithmeticFunction.moebius n : ℝ) := by
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  exact_mod_cast hmul

/-! ### The singular-series sum and its reduction -/

/-- The singular-series sum for coordinate `i`: `λ_d λ_e / φ(L)` over
    good support pairs, where `L` is the combined modulus. This is
    the object whose evaluation to `𝔖(h)` times an explicit integral
    is the classical singular-series computation. -/
noncomputable def singSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) : ℝ := by
  classical
  exact ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then lam d * lam e
      / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

/-- Triple-sum commutation, used to move the coordinate sum outside
    the pair sums. -/
theorem sum_sum_sum_comm {α γ : Type*} {s : Finset α} {u : Finset γ}
    (F : α → α → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
  calc (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ p ∈ s ×ˢ s, ∑ i ∈ u, F p.1 p.2 i :=
        (Finset.sum_product' (s := s) (t := s)
          (f := fun d e => ∑ i ∈ u, F d e i)).symm
    _ = ∑ i ∈ u, ∑ p ∈ s ×ˢ s, F p.1 p.2 i := Finset.sum_comm
    _ = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_product' (s := s) (t := s) (f := fun d e => F d e i)

/-- The BV main term for the model `li/φ` factors as a sum over
    coordinates of the li-difference times the singular-series sum:
    the li-differences do not depend on `(d, e)`, so they factor out
    of the pair sums, leaving a pure λ-sum. -/
theorem bvMainTerm_li_div_totient {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (li : ℝ → ℝ) {x y : ℕ} :
    bvMainTerm k h R lam (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) x y
      = ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
        * singSum k h R lam i := by
  have htriple : ∀ (M : ℕ → ℕ → ℝ),
      (∀ Y L, M Y L = li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) →
      ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R, ∀ i,
      lam d * lam e * bvMainSummand M h d e i x y
        = (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
          * (if goodPair h d e i then lam d * lam e
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0) := by
    intro M hM d _ e _ i
    unfold bvMainSummand
    by_cases hgood : goodPair h d e i
    · rw [if_pos hgood, if_pos hgood, hM, hM, ← sub_div]
      ring
    · rw [if_neg hgood, if_neg hgood]
      simp
  have hM : ∀ (Y L : ℕ), (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) Y L
      = li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ) := fun Y L => rfl
  calc bvMainTerm k h R lam (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) x y
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R, ∑ i,
          (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
            * (if goodPair h d e i then lam d * lam e
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
              else 0) := by
        unfold bvMainTerm
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact htriple _ hM d hd e he i
    _ = ∑ i, ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
            * (if goodPair h d e i then lam d * lam e
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
              else 0) :=
        sum_sum_sum_comm _
    _ = ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
          * singSum k h R lam i := by
        apply Finset.sum_congr rfl
        intro i _
        unfold singSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]

/-- The singular sum grouped by combined modulus: `singSum i` equals
    `∑_{L ≤ R²} (1/φ(L)) * A_i(L)`, where `A_i(L)` is the pair sum at
    modulus `L`. The level bound `L ≤ R²` (from
    `lcm_le_sq_of_mem_support`) is what keeps the modulus range
    finite and inside the BV range. Multiplicativity of `A_i` in `L`
    and evaluation of the local factors are the remaining arithmetic
    core (see the header). -/
theorem singSum_eq_sum_over_L {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    singSum k h R lam i
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
              ∧ goodPair h d e i)
            then lam d * lam e else 0) := by
  have hmem : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
        ∈ Finset.Icc 1 (R ^ 2) := by
    intro d hd e he
    obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨h1', -, -⟩ := mem_tupleSupport.mp he
    have hLne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 := by
      apply Finset.lcm_ne_zero_iff.mpr
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := h1 j
        omega
      · have hj := h1' j
        omega
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hLne, lcm_le_sq_of_mem_support hd he⟩
  have hstep1 : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then lam d * lam e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
        else 0)
        = ∑ L ∈ Finset.Icc 1 (R ^ 2),
          (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
            (if goodPair h d e i then lam d * lam e
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) := by
    intro d hd e he
    rw [Finset.sum_ite_eq', if_pos (hmem d hd e he)]
  have hstep3 : ∀ L ∈ Finset.Icc 1 (R ^ 2),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then lam d * lam e
            / ((Nat.totient L : ℕ) : ℝ) else 0) else 0))
        = (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
              ∧ goodPair h d e i)
            then lam d * lam e else 0) := by
    intro L _
    have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then lam d * lam e
            / ((Nat.totient L : ℕ) : ℝ) else 0) else 0)
        = (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then lam d * lam e else 0) := by
      intro d _ e _
      by_cases hLe : L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      · by_cases hg : goodPair h d e i
        · rw [if_pos hLe, if_pos hg, if_pos ⟨hLe.symm, hg⟩,
            mul_comm (1 / ((Nat.totient L : ℕ) : ℝ)) _, mul_one_div]
        · rw [if_pos hLe, if_neg hg, if_neg (fun hcon => hg hcon.2), mul_zero]
      · rw [if_neg hLe, if_neg (fun hcon => hLe hcon.1.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  calc singSum k h R lam i
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          (if goodPair h d e i then lam d * lam e
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0) := rfl
    _ = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
          (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
            (if goodPair h d e i then lam d * lam e
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        exact hstep1 d hd e he
    _ = ∑ L ∈ Finset.Icc 1 (R ^ 2), ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
            (if goodPair h d e i then lam d * lam e
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) :=
        sum_sum_sum_comm _
    _ = ∑ L ∈ Finset.Icc 1 (R ^ 2),
          (1 / ((Nat.totient L : ℕ) : ℝ)) *
            (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
              if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                ∧ goodPair h d e i)
              then lam d * lam e else 0) := by
        apply Finset.sum_congr rfl
        intro L hL
        exact hstep3 L hL

/-! ### The chained second-moment bound for the Selberg weight -/

/-- Chained payoff: the second moment with the Selberg weight, bounded
    by the τ-weighted mass squared times the BV endpoint error terms.
    This chains the instantiation corollary
    `secondMoment_bvErrBound_of_bvSumBound` with the τ-weighted mass
    identity `lambdaMass_lamSelberg_eq`. -/
theorem secondMoment_bvErrBound_selberg {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (deg : ℕ)
    {x y : ℕ} (hxy : x ≤ y)
    {η A' C : ℝ} (hC : 0 ≤ C) (li : ℝ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - li (Y' : ℝ) / (Nat.totient q : ℝ))
          ≤ C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')))
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (secondMoment k h R (lamSelberg k R deg) x y
        - bvMainTerm k h R (lamSelberg k R deg)
          (fun Y L => li (Y : ℝ) / (Nat.totient L : ℝ)) x y)
      ≤ (∑ D ∈ Finset.Icc 1 R,
          (tupleProdCount k D : ℝ)
            * |(ArithmeticFunction.moebius D : ℝ)
              * (1 - Real.log D / Real.log R) ^ deg|) ^ 2
        * ((R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ)
            * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + C * (((x + h i : ℕ) : ℝ)
            * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ)) := by
  have hmain := secondMoment_bvErrBound_of_bvSumBound h R (lamSelberg k R deg)
    hxy hC li hBV hlevel hY2
  have hnn : 0 ≤ (R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ)
      * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
    + C * (((x + h i : ℕ) : ℝ)
      * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ) := by
    have hterm : ∀ i, 0 ≤ C * (((y + h i : ℕ) : ℝ)
        * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
      + C * (((x + h i : ℕ) : ℝ)
        * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')) := by
      intro i
      have hy : (1 : ℝ) < ((y + h i : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < y + h i by have h2 := (hY2 i).1; omega)
      have hx : (1 : ℝ) < ((x + h i : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < x + h i by have h2 := (hY2 i).2; omega)
      have hlogy : (0 : ℝ) < Real.log ((y + h i : ℕ) : ℝ) := Real.log_pos hy
      have hlogx : (0 : ℝ) < Real.log ((x + h i : ℕ) : ℝ) := Real.log_pos hx
      have hrpowy : (0 : ℝ) < Real.log ((y + h i : ℕ) : ℝ) ^ (-A') :=
        Real.rpow_pos_of_pos hlogy _
      have hrpowx : (0 : ℝ) < Real.log ((x + h i : ℕ) : ℝ) ^ (-A') :=
        Real.rpow_pos_of_pos hlogx _
      have hypos : (0 : ℝ) < ((y + h i : ℕ) : ℝ) := by linarith
      have hxpos : (0 : ℝ) < ((x + h i : ℕ) : ℝ) := by linarith
      exact add_nonneg (mul_nonneg hC (mul_nonneg hypos.le hrpowy.le))
        (mul_nonneg hC (mul_nonneg hxpos.le hrpowx.le))
    exact add_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Finset.sum_nonneg (fun i _ => hterm i)))
      (Nat.cast_nonneg _)
  exact le_trans hmain
    (mul_le_mul_of_nonneg_right lambdaMass_lamSelberg_eq.le hnn)


/-! ### The harmonic bound -/

/-- The one-line analytic input: `1/(d+1) ≤ log(d+1) - log d`, from
    `log x ≤ x - 1` applied to `x = d/(d+1)`. -/
theorem inv_succ_le_log_sub {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / ((d : ℝ) + 1) ≤ Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hfrac : (0 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) := by positivity
  have hle := Real.log_le_sub_one_of_pos hfrac
  rw [Real.log_div (ne_of_gt hdpos) (ne_of_gt (by positivity : (0 : ℝ) < (d : ℝ) + 1))] at hle
  have hdiv : (d : ℝ) / ((d : ℝ) + 1) - 1 = - (1 / ((d : ℝ) + 1)) := by
    field_simp
    ring
  rw [hdiv] at hle
  linarith

/-- The harmonic bound `∑_{d ≤ R} 1/d ≤ 1 + log R`, by induction. -/
theorem sum_Icc_inv_le : ∀ {R : ℕ}, 1 ≤ R →
    ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (R : ℝ) := by
  intro R
  induction R with
  | zero => intro h; omega
  | succ n ih =>
    intro hR
    by_cases hn : n = 0
    · subst hn
      rw [Finset.Icc_self]
      simp
    · have hn1 : 1 ≤ n := by omega
      have ih' := ih hn1
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hstep : (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤
          Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) := by
        have h := inv_succ_le_log_sub (d := n) hn1
        push_cast at h ⊢
        exact h
      push_cast at hstep ⊢
      linarith

/-! ### The divisor double count -/

/-- Multiples count: the multiples of `d` in `Icc 1 R` are exactly
    `R/d` in number, via `D = d * m` with `m ≤ R/d`. -/
theorem card_multiples_Icc {d R : ℕ} (hd : 1 ≤ d) :
    ((Finset.Icc 1 R).filter (fun D => d ∣ D)).card = R / d := by
  have hdpos : 0 < d := by omega
  have himg : (Finset.Icc 1 R).filter (fun D => d ∣ D)
      = (Finset.Icc 1 (R / d)).image (fun m => d * m) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hD1, hDR⟩, hdiv⟩
      obtain ⟨m, rfl⟩ := hdiv
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm] at hD1; simp at hD1
        · exact hm
      · exact (Nat.le_div_iff_mul_le hdpos).mpr (by rwa [mul_comm])
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · have h := (Nat.le_div_iff_mul_le hdpos).mp hmR
        rwa [mul_comm] at h
  have hinj : Set.InjOn (fun m => d * m) (Finset.Icc 1 (R / d)) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  rw [himg, Finset.card_image_of_injOn hinj, Nat.card_Icc]
  simp

/-- The divisor double count: `∑_{D ≤ R} τ(D) = ∑_{d ≤ R} R/d`. -/
theorem sum_divisors_card_eq (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, (Nat.divisors D).card = ∑ d ∈ Finset.Icc 1 R, R / d := by
  have hpair : ∀ D ∈ Finset.Icc 1 R, (Nat.divisors D).card
      = ((Finset.Icc 1 R).filter (fun d => d ∣ D)).card := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdiv, hD0⟩
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · rw [hd0] at hdiv
          have hD00 : D = 0 := by simpa using hdiv
          exact (hD0 hD00).elim
        · exact hdpos
      exact ⟨⟨hd1, le_trans (Nat.le_of_dvd (by omega : 0 < D) hdiv) hD.2⟩, hdiv⟩
    · rintro ⟨⟨_, _⟩, hdiv⟩
      exact ⟨hdiv, by omega⟩
  rw [Finset.sum_congr rfl hpair]
  have h1 : ∀ D ∈ Finset.Icc 1 R, ((Finset.Icc 1 R).filter (fun d => d ∣ D)).card
      = ∑ d ∈ Finset.Icc 1 R, (if d ∣ D then (1 : ℕ) else 0) := by
    intro D _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [Finset.sum_boole]
  exact card_multiples_Icc hd.1

/-- Hence `∑_{D ≤ R} τ(D) ≤ R * (1 + log R)`. -/
theorem sum_tau_le {R : ℕ} (hR : 1 ≤ R) :
    (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ)) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) := by
  calc (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ))
      = ((∑ D ∈ Finset.Icc 1 R, (Nat.divisors D).card : ℕ) : ℝ) := by
        push_cast
        rfl
    _ = ((∑ d ∈ Finset.Icc 1 R, R / d : ℕ) : ℝ) := by rw [sum_divisors_card_eq]
    _ = ∑ d ∈ Finset.Icc 1 R, ((R / d : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact Nat.cast_div_le
    _ = (R : ℝ) * ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [mul_one_div]
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_Icc_inv_le hR) (by positivity)

/-! ### The divisor convolution identity for `τ_k` -/

/-- The `k`-fold divisor function satisfies the convolution identity
    `τ_{k+1}(D) = ∑_{e ∣ D} τ_k(D/e)`: split a `(k+1)`-tuple at its
    first coordinate. -/
theorem tupleProdCount_succ {k D : ℕ} :
    tupleProdCount (k + 1) D = ∑ e ∈ Nat.divisors D, tupleProdCount k (D / e) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0, Nat.divisors_zero, Finset.sum_empty]
    simp only [tupleProdCount]
    rw [Finset.card_eq_zero]
    ext d
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hd
    have h0 := (Fintype.mem_piFinset.mp hd.1) 0
    rw [Finset.mem_Icc] at h0
    omega
  · have hD1 : 1 ≤ D := hDpos
    -- The defining finset and its first-coordinate fibers.
    set S := (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
      (fun d => ∏ i, d i = D) with hS
    have hmaps : ∀ d ∈ S, d 0 ∈ Finset.Icc 1 D := by
      intro d hd
      rw [hS] at hd
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
      exact hd.1 0
    have hcard : S.card = ∑ e ∈ Finset.Icc 1 D,
        (S.filter (fun d => d 0 = e)).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
    -- Fiber cards.
    have hfib : ∀ e ∈ Finset.Icc 1 D, (S.filter (fun d => d 0 = e)).card
        = if e ∣ D then tupleProdCount k (D / e) else 0 := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases hdiv : e ∣ D
      · rw [if_pos hdiv]
        have hepos : 0 < e := by
          rcases Nat.eq_zero_or_pos e with he0 | hepos
          · omega
          · exact hepos
        have heD : e ≤ D := Nat.le_of_dvd hDpos hdiv
        have hDe : D / e * e = D := Nat.div_mul_cancel hdiv
        have hDe1 : 1 ≤ D / e := by
          rw [Nat.le_div_iff_mul_le hepos]
          simpa using heD
        -- Bijection: tail / cons.
        have hbij : (S.filter (fun d => d 0 = e)).card
            = ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 (D / e))).filter
              (fun t => ∏ i, t i = D / e)).card := by
          apply Finset.card_bij (fun d _ => Fin.tail d)
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            obtain ⟨hdS, hd0⟩ := hd
            rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hdS
            obtain ⟨hdmem, hdprod⟩ := hdS
            have htailprod : ∏ i, Fin.tail d i = D / e := by
              have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
              rw [hd0, hdprod] at h1
              have h2 : e * ∏ i, Fin.tail d i = e * (D / e) := by
                rw [← h1, Nat.mul_div_cancel' hdiv]
              exact Nat.eq_of_mul_eq_mul_left hepos h2
            refine ⟨?_, htailprod⟩
            rw [Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_Icc]
            have hmem : d i.succ ∈ Finset.Icc 1 D := hdmem i.succ
            rw [Finset.mem_Icc] at hmem
            refine ⟨hmem.1, ?_⟩
            have hdvd : d i.succ ∣ ∏ j, Fin.tail d j :=
              Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
            rw [htailprod] at hdvd
            exact Nat.le_of_dvd (by omega : 0 < D / e) hdvd
          · intro d hd e' hd' hde'
            rw [Finset.mem_filter] at hd hd'
            obtain ⟨-, hd0⟩ := hd
            obtain ⟨-, he'0⟩ := hd'
            have hd_eq : d = Fin.cons e (Fin.tail d) := by
              rw [← hd0]; exact (Fin.cons_self_tail d).symm
            have he'_eq : e' = Fin.cons e (Fin.tail e') := by
              rw [← he'0]; exact (Fin.cons_self_tail e').symm
            rw [hd_eq, he'_eq, hde']
          · intro t ht
            rw [Finset.mem_filter, Fintype.mem_piFinset] at ht
            obtain ⟨htmem, htprod⟩ := ht
            refine ⟨Fin.cons e t, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨?_, ?_⟩
              · rw [hS, Finset.mem_filter, Fintype.mem_piFinset]
                refine ⟨?_, ?_⟩
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · rw [Fin.cons_zero]
                    exact Finset.mem_Icc.mpr ⟨he.1, heD⟩
                  · intro j
                    rw [Fin.cons_succ]
                    have hmi := htmem j
                    rw [Finset.mem_Icc] at hmi ⊢
                    exact ⟨hmi.1, le_trans hmi.2 (Nat.div_le_self D e)⟩
                · rw [Fin.prod_univ_succ, Fin.cons_zero]
                  simp only [Fin.cons_succ]
                  rw [htprod, Nat.mul_div_cancel' hdiv]
              · rw [Fin.cons_zero]
            · rw [Fin.tail_cons]
        rw [hbij]
        rfl
      · rw [if_neg hdiv]
        rw [Finset.card_eq_zero]
        ext d
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        intro hd
        obtain ⟨hdS, hd0⟩ := hd
        rw [hS, Finset.mem_filter] at hdS
        obtain ⟨-, hdprod⟩ := hdS
        have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
        rw [hd0, hdprod] at h1
        exact hdiv ⟨∏ i, Fin.tail d i, h1⟩
    have hTS : tupleProdCount (k + 1) D = S.card := rfl
    rw [hTS, hcard]
    rw [Finset.sum_congr rfl hfib]
    rw [← Finset.sum_filter]
    congr 1

/-! ### The divisor reindexing and the general `τ_k` bound -/

/-- Reindexing: summing `f(D/e)` over `e ∣ D`, `D ≤ R`, is the same
    as summing `f(m)` over `m ≤ R/e`, `e ≤ R`. -/
theorem sum_divisors_reindex (f : ℕ → ℝ) (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, f (D / e)
      = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), f m := by
  have h1 : ∀ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, f (D / e)
      = ∑ e ∈ Finset.Icc 1 R, (if e ∣ D then f (D / e) else 0) := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdiv, hD0⟩
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with he0 | hepos
        · rw [he0] at hdiv
          have hD00 : D = 0 := by simpa using hdiv
          exact (hD0 hD00).elim
        · exact hepos
      exact ⟨⟨he1, le_trans (Nat.le_of_dvd (by omega : 0 < D) hdiv) hD.2⟩, hdiv⟩
    · rintro ⟨⟨-, -⟩, hdiv⟩
      exact ⟨hdiv, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_Icc] at he
  by_cases he0 : e = 0
  · rw [he0] at he; omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have himg : (Finset.Icc 1 R).filter (fun D => e ∣ D)
        = (Finset.Icc 1 (R / e)).image (fun m => e * m) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hD1, hDR⟩, hdiv⟩
        obtain ⟨m, rfl⟩ := hdiv
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with hm | hm
          · rw [hm] at hD1; simp at hD1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hepos).mpr (by rwa [mul_comm])
      · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        · have h := (Nat.le_div_iff_mul_le hepos).mp hmR
          rwa [mul_comm] at h
    have hinj : Set.InjOn (fun m => e * m) (Finset.Icc 1 (R / e)) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hepos hab
    rw [← Finset.sum_filter, himg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_comm, Nat.mul_div_cancel _ hepos]

/-- The general bound `∑_{D ≤ R} τ_{k+1}(D) ≤ R * (1 + log R)^k`. -/
theorem sum_tupleProdCount_le : ∀ (k : ℕ) {R : ℕ}, 1 ≤ R →
    ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
    intro R hR
    show ∑ D ∈ Finset.Icc 1 R, (tupleProdCount 1 D : ℝ) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 0
    have h1 : ∀ D ∈ Finset.Icc 1 R, (tupleProdCount 1 D : ℝ) = 1 := by
      intro D hD
      rw [Finset.mem_Icc] at hD
      have hset : (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 D)).filter
          (fun d => ∏ i, d i = D) = {fun _ => D} := by
        ext d
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨hdmem, hdprod⟩
          rw [Fin.prod_univ_one] at hdprod
          funext i
          fin_cases i
          exact hdprod
        · intro hd
          rw [hd]
          refine ⟨?_, ?_⟩
          · intro i
            fin_cases i
            exact Finset.mem_Icc.mpr ⟨hD.1, le_rfl⟩
          · rw [Fin.prod_univ_one]
      have hcard : tupleProdCount 1 D = 1 := by
        simp only [tupleProdCount]
        rw [hset, Finset.card_singleton]
      rw [hcard, Nat.cast_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Icc]
    simp [pow_zero]
  | succ k ih =>
    intro R hR
    have hLHS : ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1 + 1) D : ℝ)
        = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e),
          (tupleProdCount (k + 1) m : ℝ) := by
      have h1 : ∀ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1 + 1) D : ℝ)
          = ∑ e ∈ Nat.divisors D, (tupleProdCount (k + 1) (D / e) : ℝ) := by
        intro D _
        rw [tupleProdCount_succ, Nat.cast_sum]
      rw [Finset.sum_congr rfl h1]
      exact sum_divisors_reindex (fun m => (tupleProdCount (k + 1) m : ℝ)) R
    rw [hLHS]
    have hbound : ∀ e ∈ Finset.Icc 1 R,
        ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
          ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases h0 : R / e = 0
      · rw [h0]
        have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro m hm
          rw [Finset.mem_Icc] at hm
          omega
        rw [hempty, Finset.sum_empty]
        positivity
      · have h1 : 1 ≤ R / e := Nat.one_le_iff_ne_zero.mpr h0
        have ih' := ih h1
        have hcast : ((R / e : ℕ) : ℝ) ≤ (R : ℝ) / (e : ℝ) := Nat.cast_div_le
        have hlog : Real.log ((R / e : ℕ) : ℝ) ≤ Real.log (R : ℝ) := by
          by_cases hpos : (0 : ℝ) < ((R / e : ℕ) : ℝ)
          · exact Real.log_le_log hpos (by exact_mod_cast Nat.div_le_self R e)
          · have hz : ((R / e : ℕ) : ℝ) = 0 :=
              le_antisymm (le_of_not_gt hpos) (by positivity)
            rw [hz, Real.log_zero]
            exact Real.log_nonneg (by exact_mod_cast hR)
        have hnn1 : (0 : ℝ) ≤ 1 + Real.log ((R / e : ℕ) : ℝ) := by
          have hlognn : (0 : ℝ) ≤ Real.log ((R / e : ℕ) : ℝ) :=
            Real.log_nonneg (by exact_mod_cast h1)
          linarith
        have hpow : (1 + Real.log ((R / e : ℕ) : ℝ)) ^ k ≤
            (1 + Real.log (R : ℝ)) ^ k :=
          pow_le_pow_left₀ hnn1 (by linarith) k
        calc ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
            ≤ ((R / e : ℕ) : ℝ) * (1 + Real.log ((R / e : ℕ) : ℝ)) ^ k := ih'
          _ ≤ ((R : ℝ) / (e : ℝ)) * (1 + Real.log (R : ℝ)) ^ k :=
              mul_le_mul hcast hpow (pow_nonneg hnn1 k) (by positivity)
          _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) := by ring
    calc ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
        ≤ ∑ e ∈ Finset.Icc 1 R, (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) :=
          Finset.sum_le_sum hbound
      _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * ∑ e ∈ Finset.Icc 1 R, (1 : ℝ) / (e : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 + Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_le hR) (by positivity)
      _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ (k + 1) := by
          rw [pow_succ]; ring

/-! ### The Selberg λ-mass bound -/

/-- The divisor-weighted Selberg mass sum is at most `R * (1 + log R)^k`:
    each term is at most `τ_{k+1}(D)`, since `|μ| ≤ 1` and the cutoff
    factor lies in `[0,1]` on the range. -/
theorem selbergMassSum_le {k R deg : ℕ} (hR : 2 ≤ R) :
    ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ)
      * |(ArithmeticFunction.moebius D : ℝ)
        * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
      ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by
  calc ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ)
        * |(ArithmeticFunction.moebius D : ℝ)
          * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
      ≤ ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        rw [Finset.mem_Icc] at hD
        have hlogR : (0 : ℝ) < Real.log (R : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < R by omega))
        have hlogD_nn : (0 : ℝ) ≤ Real.log (D : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hD.1)
        have hlogD_le : Real.log (D : ℝ) ≤ Real.log (R : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < D))
            (by exact_mod_cast hD.2)
        have hfrac_nn : (0 : ℝ) ≤ Real.log (D : ℝ) / Real.log (R : ℝ) :=
          div_nonneg hlogD_nn hlogR.le
        have hfrac_le : Real.log (D : ℝ) / Real.log (R : ℝ) ≤ 1 :=
          (div_le_one hlogR).mpr hlogD_le
        have hfac_nn : (0 : ℝ) ≤ 1 - Real.log (D : ℝ) / Real.log (R : ℝ) := by
          linarith
        have hfac_le : 1 - Real.log (D : ℝ) / Real.log (R : ℝ) ≤ 1 := by linarith
        have hpow_nn : (0 : ℝ) ≤
            (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg :=
          pow_nonneg hfac_nn _
        have hpow_le : (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg ≤ 1 :=
          pow_le_one₀ hfac_nn hfac_le
        have hmu : |(ArithmeticFunction.moebius D : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hfac : |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hpow_nn]
          calc |(ArithmeticFunction.moebius D : ℝ)|
                * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg
              ≤ 1 * 1 := mul_le_mul hmu hpow_le hpow_nn zero_le_one
            _ = 1 := one_mul 1
        calc (tupleProdCount (k + 1) D : ℝ)
              * |(ArithmeticFunction.moebius D : ℝ)
                * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
            ≤ (tupleProdCount (k + 1) D : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hfac (by positivity)
          _ = (tupleProdCount (k + 1) D : ℝ) := mul_one _
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k :=
        sum_tupleProdCount_le k (by omega)

/-- The Selberg λ-mass with the crude `|support|²` bound replaced by
    the τ-weighted polylog bound: `Λ ≤ (R * (1 + log R)^k)²` for tuple
    size `k+1`. Compare the crude bound `Λ ≤ |support|² ≤ R^{2k+2}`:
    this saves a factor of roughly `R^{2k}` against the crude bound. -/
theorem lambdaMass_lamSelberg_le_tau {k R deg : ℕ} (hR : 2 ≤ R) :
    (∑ d ∈ tupleSupport (k + 1) R, ∑ e ∈ tupleSupport (k + 1) R,
      |lamSelberg (k + 1) R deg d * lamSelberg (k + 1) R deg e|)
      ≤ ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ k) ^ 2 := by
  rw [lambdaMass_lamSelberg_eq]
  exact pow_le_pow_left₀ (by positivity) (selbergMassSum_le hR) 2


/-! ### Pairwise coprimality on squarefree-product support -/

/-- On squarefree-product support the coordinates are pairwise
    coprime: the gcd of two distinct coordinates squares-divides
    the product, and squarefree forces it to be `1`. -/
theorem pairwise_coprime_of_squarefree_prod {k : ℕ} {d : Fin k → ℕ}
    (_hd1 : ∀ i, 1 ≤ d i) (hsq : Squarefree (∏ i, d i))
    {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by
  have hjerase : d j ∣ ∏ i' ∈ Finset.univ.erase i, d i' :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have hprod : ∏ i', d i' = d i * ∏ i' ∈ Finset.univ.erase i, d i' :=
    (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
  have hmul : d i * d j ∣ ∏ i', d i' := by
    rw [hprod]
    exact mul_dvd_mul_left (d i) hjerase
  have hg1 : Nat.gcd (d i) (d j) ∣ d i := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (d i) (d j) ∣ d j := Nat.gcd_dvd_right _ _
  have hgg : Nat.gcd (d i) (d j) * Nat.gcd (d i) (d j) ∣ ∏ i', d i' :=
    dvd_trans (mul_dvd_mul hg1 hg2) hmul
  have hu : IsUnit (Nat.gcd (d i) (d j)) := hsq _ hgg
  exact Nat.isUnit_iff.mp hu

/-! ### A pairwise-coprime family divides a common multiple -/

/-- If a family is pairwise coprime and every coordinate divides `L`,
    then the product divides `L` (induction on the tuple dimension). -/
theorem prod_dvd_of_pairwise_coprime :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := by
  intro k
  induction k with
  | zero =>
    intro d L _ _
    simp
  | succ k ih =>
    intro d L hcop hdvd
    rw [Fin.prod_univ_succ]
    have hcop_tail : ∀ i j, i ≠ j → Nat.Coprime (Fin.tail d i) (Fin.tail d j) :=
      fun i j hij => hcop i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
    have hdvd_tail : ∀ i, Fin.tail d i ∣ L := fun i => hdvd i.succ
    have htail : ∏ i, Fin.tail d i ∣ L := ih hcop_tail hdvd_tail
    have hcop0 : Nat.Coprime (d 0) (∏ i, Fin.tail d i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i _
      exact hcop 0 i.succ (Fin.succ_ne_zero i).symm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop0 (hdvd 0) htail

/-! ### The combined modulus is the lcm of the products -/

/-- On squarefree-product support, the combined modulus
    `Finset.lcm univ (fun j => Nat.lcm (d j) (e j))` equals
    `Nat.lcm (∏ d) (∏ e)`. -/
theorem combined_lcm_eq {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := by
  apply dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    apply Nat.lcm_dvd
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · apply prod_dvd_of_pairwise_coprime
        (fun i j hij => pairwise_coprime_of_squarefree_prod hd1 hsqd hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_left (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))
    · apply prod_dvd_of_pairwise_coprime
        (fun i j hij => pairwise_coprime_of_squarefree_prod he1 hsqe hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_right (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))

/-! ### Counting fibers: from support fibers to `τ_{k+1}` -/

/-- The fiber of the support over a product `D` has card at most
    `τ_k(D)`: a support tuple with product `D` has all entries
    between `1` and `D`, hence is a `k`-factorization of `D`. -/
theorem card_filter_tupleSupport_prod_le {k R D : ℕ} :
    ((tupleSupport k R).filter (fun d => ∏ i, d i = D)).card
      ≤ tupleProdCount k D := by
  apply Finset.card_le_card
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdmem, hprod⟩ := hd
  obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hdmem
  rw [Finset.mem_filter]
  refine ⟨?_, hprod⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  refine ⟨h1 i, ?_⟩
  have hle : d i ≤ ∏ j, d j :=
    Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
  rw [hprod] at hle
  exact hle

/-- Summing `τ_k` over the divisors of `L` gives `τ_{k+1}(L)`: the
    convolution identity plus the divisor involution `D ↦ L / D`. -/
theorem sum_tupleProdCount_divisors {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors, tupleProdCount k D = tupleProdCount (k + 1) L := by
  rw [tupleProdCount_succ]
  apply Finset.sum_bij (fun D _ => L / D)
  · intro D hD
    rw [Nat.mem_divisors] at hD ⊢
    exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
  · intro a ha b hb hab
    rw [Nat.mem_divisors] at ha hb
    have h1 : a = L / (L / a) := (Nat.div_div_self ha.1 hL).symm
    have h2 : b = L / (L / b) := (Nat.div_div_self hb.1 hL).symm
    rw [h1, h2, hab]
  · intro D hD
    rw [Nat.mem_divisors] at hD
    refine ⟨L / D, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
    · exact Nat.div_div_self hD.1 hL
  · intro D hD
    rw [Nat.div_div_self (Nat.mem_divisors.mp hD).1 hL]

/-- The Selberg fiber count at `L`: support pairs, good at `i`,
    combined modulus `L`, both products squarefree. -/
noncomputable def fiberCountSelberg {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k) (L : ℕ) : ℕ :=
  ((tupleSupport k R ×ˢ tupleSupport k R).filter
    (fun p => goodPair h p.1 p.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
      Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card

/-- The Selberg fiber count at `L` is at most `τ_{k+1}(L)²`. -/
theorem fiberCountSelberg_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k) (L : ℕ) :
    fiberCountSelberg h R i L ≤ tupleProdCount (k + 1) L ^ 2 := by
  by_cases hL0 : L = 0
  · subst hL0
    have hempty : fiberCountSelberg h R i 0 = 0 := by
      rw [fiberCountSelberg, Finset.card_eq_zero]
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨hprodmem, -, hF, -, -⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hp1
      obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp hp2
      have hFne : Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) ≠ 0 := by
        apply Finset.lcm_ne_zero_iff.mpr
        intro j _
        apply Nat.lcm_ne_zero
        · have hj := hd1 j
          omega
        · have hj := he1 j
          omega
      exact hFne hF
    rw [hempty]
    exact Nat.zero_le _
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
    -- Each fiber pair has both products dividing L.
    have hprod_dvd : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
          Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j)),
        (∏ j, p.1 j) ∣ L ∧ (∏ j, p.2 j) ∣ L := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hprodmem, -, hF, hsq1, hsq2⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hp1
      obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp hp2
      constructor
      · apply prod_dvd_of_pairwise_coprime
          (fun a b hab => pairwise_coprime_of_squarefree_prod hd1 hsq1 hab)
        intro j
        rw [← hF]
        exact dvd_trans (Nat.dvd_lcm_left (p.1 j) (p.2 j))
          (Finset.dvd_lcm (Finset.mem_univ j))
      · apply prod_dvd_of_pairwise_coprime
          (fun a b hab => pairwise_coprime_of_squarefree_prod he1 hsq2 hab)
        intro j
        rw [← hF]
        exact dvd_trans (Nat.dvd_lcm_right (p.1 j) (p.2 j))
          (Finset.dvd_lcm (Finset.mem_univ j))
    -- The fiber sits inside the product of the one-sided divisor fibers.
    have hsub : ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
          Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j)))
        ⊆ (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) ×ˢ
          (tupleSupport k R).filter (fun e => ∏ j, e j ∣ L) := by
      intro p hp
      obtain ⟨hdvd1, hdvd2⟩ := hprod_dvd p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hprodmem, -⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      rw [Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨hp1, hdvd1⟩, Finset.mem_filter.mpr ⟨hp2, hdvd2⟩⟩
    -- One-sided count: fiberwise over divisors, then the τ identity.
    have hone : ∀ (s : Finset (Fin k → ℕ)),
        s = (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) →
        s.card ≤ tupleProdCount (k + 1) L := by
      intro s hs
      rw [hs]
      have hmaps : ∀ d ∈ (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L),
          (∏ j, d j) ∈ L.divisors := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, hL0⟩
      calc ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).card
          = ∑ D ∈ L.divisors,
              (((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).filter
                (fun d => ∏ j, d j = D)).card :=
            Finset.card_eq_sum_card_fiberwise hmaps
        _ ≤ ∑ D ∈ L.divisors, tupleProdCount k D := by
            apply Finset.sum_le_sum
            intro D _
            calc (((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).filter
                    (fun d => ∏ j, d j = D)).card
                ≤ ((tupleSupport k R).filter (fun d => ∏ j, d j = D)).card := by
                  apply Finset.card_le_card
                  intro d hd
                  rw [Finset.mem_filter] at hd
                  obtain ⟨hd1, hd2⟩ := hd
                  rw [Finset.mem_filter]
                  exact ⟨(Finset.mem_filter.mp hd1).1, hd2⟩
              _ ≤ tupleProdCount k D := card_filter_tupleSupport_prod_le
        _ = tupleProdCount (k + 1) L := sum_tupleProdCount_divisors hL0
    calc fiberCountSelberg h R i L
        = ((tupleSupport k R ×ˢ tupleSupport k R).filter
            (fun p => goodPair h p.1 p.2 i ∧
              Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
              Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card := rfl
      _ ≤ ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) ×ˢ
            (tupleSupport k R).filter (fun e => ∏ j, e j ∣ L)).card :=
          Finset.card_le_card hsub
      _ = ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).card
            * ((tupleSupport k R).filter (fun e => ∏ j, e j ∣ L)).card :=
          Finset.card_product _ _
      _ ≤ tupleProdCount (k + 1) L * tupleProdCount (k + 1) L :=
          Nat.mul_le_mul (hone _ rfl) (hone _ rfl)
      _ = tupleProdCount (k + 1) L ^ 2 := (pow_two _).symm

/-! ### The fiber-weight bound for the Selberg weight -/

/-- The fiber weight for the Selberg weight at modulus `L` is at most
    `τ_{k+1}(L)²`: non-squarefree terms vanish by Möbius, and the
    surviving terms are at most `1`. -/
theorem fiberWeight_lamSelberg_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (deg : ℕ)
    (hR : 2 ≤ R) (i : Fin k) (L : ℕ) :
    fiberWeight h R (lamSelberg k R deg) i L
      ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
  classical
  have hterm : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
      (fun p => goodPair h p.1 p.2 i ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
      abs (lamSelberg k R deg p.1 * lamSelberg k R deg p.2)
        ≤ (if Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j) then (1 : ℝ) else 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hprodmem, -⟩ := hp
    have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
    have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
    by_cases hsq1 : Squarefree (∏ j, p.1 j)
    · by_cases hsq2 : Squarefree (∏ j, p.2 j)
      · rw [if_pos ⟨hsq1, hsq2⟩, abs_mul]
        calc abs (lamSelberg k R deg p.1) * abs (lamSelberg k R deg p.2)
            ≤ 1 * 1 := mul_le_mul (abs_lamSelberg_le_one hp1 hR)
              (abs_lamSelberg_le_one hp2 hR) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · rw [if_neg (fun hcon => hsq2 hcon.2), lamSelberg_eq_zero_of_not_squarefree hsq2]
        simp
    · rw [if_neg (fun hcon => hsq1 hcon.1), lamSelberg_eq_zero_of_not_squarefree hsq1]
      simp
  have hfilter_eq : ((tupleSupport k R ×ˢ tupleSupport k R).filter
      (fun p => goodPair h p.1 p.2 i ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)).filter
      (fun p => Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))
      = (tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
          Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j)) := by
    ext p
    simp only [Finset.mem_filter, and_assoc]
  calc fiberWeight h R (lamSelberg k R deg) i L
      = ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
        abs (lamSelberg k R deg p.1 * lamSelberg k R deg p.2) := rfl
    _ ≤ ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
        (if Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = (((tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)).filter
          (fun p => Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card := by
        rw [Finset.sum_boole]
    _ = (fiberCountSelberg h R i L : ℝ) := by
        rw [hfilter_eq]
        rfl
    _ ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
        exact_mod_cast fiberCountSelberg_le h R i L


/-! ### The divisor-weighted error sum -/

/-- The divisor-weighted error sum at height `Y'`, range `Q`,
    tuple dimension `k`: the sum over `L ≤ Q` of `τ_{k+1}(L)²`
    times the max coprime-residue error at modulus `L`. This is
    exactly the sum the grouped bound + Selberg fiber bound
    produce at each interval endpoint (with `Q = R²`). -/
noncomputable def divWeightedErrSum (M : ℕ → ℕ → ℝ) (Y' Q : ℕ) (k : ℕ) : ℝ :=
  ∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L

/-! ### Bridge: fiber-weighted sums are divisor-weighted sums -/

/-- The fiber-weighted error sum at one coordinate is at most the
    sum of the two divisor-weighted endpoint sums: termwise, the
    Selberg fiber weight is at most `τ_{k+1}(L)²`, and the errors
    are nonnegative. -/
theorem fiberWeight_sum_le_divWeightedErrSum {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (M : ℕ → ℕ → ℝ) (i : Fin k) (Y₁ Y₂ : ℕ) :
    ∑ L ∈ Finset.range (R ^ 2 + 1),
        fiberWeight h R (lamSelberg k R deg) i L
          * (maxCoprimeErr M Y₁ L + maxCoprimeErr M Y₂ L)
      ≤ divWeightedErrSum M Y₁ (R ^ 2) k + divWeightedErrSum M Y₂ (R ^ 2) k := by
  classical
  have hterm : ∀ L ∈ Finset.range (R ^ 2 + 1),
      fiberWeight h R (lamSelberg k R deg) i L
          * (maxCoprimeErr M Y₁ L + maxCoprimeErr M Y₂ L)
        ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2
          * (maxCoprimeErr M Y₁ L + maxCoprimeErr M Y₂ L) := by
    intro L _
    exact mul_le_mul_of_nonneg_right (fiberWeight_lamSelberg_le h R deg hR i L)
      (add_nonneg (maxCoprimeErr_nonneg _ _ _) (maxCoprimeErr_nonneg _ _ _))
  calc (∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R (lamSelberg k R deg) i L
            * (maxCoprimeErr M Y₁ L + maxCoprimeErr M Y₂ L))
      ≤ ∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2
            * (maxCoprimeErr M Y₁ L + maxCoprimeErr M Y₂ L) :=
        Finset.sum_le_sum hterm
    _ = (∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y₁ L)
        + (∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y₂ L) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun L _ => mul_add _ _ _)
    _ = divWeightedErrSum M Y₁ (R ^ 2) k + divWeightedErrSum M Y₂ (R ^ 2) k := rfl

/-! ### Conditional assembly: divisor-weighted hypothesis implies the error bound -/

/-- Conditional assembly: under a divisor-weighted BV hypothesis
    at every interval endpoint (bound function `E`, arbitrary —
    the assembly does not care what shape `E` has), the
    second-moment error for the Selberg weight is at most the sum
    of the endpoint bounds plus the bad-pair term `Λ·k`. -/
theorem secondMoment_divWeightedBV_bound {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (E : ℕ → ℝ)
    (hDiv : ∀ i, divWeightedErrSum M (y + h i) (R ^ 2) k ≤ E (y + h i) ∧
      divWeightedErrSum M (x + h i) (R ^ 2) k ≤ E (x + h i)) :
    abs (secondMoment k h R (lamSelberg k R deg) x y
        - bvMainTerm k h R (lamSelberg k R deg) M x y)
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lamSelberg k R deg d * lamSelberg k R deg e)) * (k : ℝ) := by
  classical
  have hgrouped := secondMoment_groupedErrBound k h R (lamSelberg k R deg) M hxy wit hwit
  have hper : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
        fiberWeight h R (lamSelberg k R deg) i L
          * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
      ≤ E (y + h i) + E (x + h i) := by
    intro i
    exact le_trans (fiberWeight_sum_le_divWeightedErrSum h R deg hR M i (y + h i) (x + h i))
      (add_le_add (hDiv i).1 (hDiv i).2)
  calc abs (secondMoment k h R (lamSelberg k R deg) x y
        - bvMainTerm k h R (lamSelberg k R deg) M x y)
      ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          fiberWeight h R (lamSelberg k R deg) i L
            * (maxCoprimeErr M (y + h i) L + maxCoprimeErr M (x + h i) L))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lamSelberg k R deg d * lamSelberg k R deg e)) * (k : ℝ) :=
        hgrouped
    _ ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lamSelberg k R deg d * lamSelberg k R deg e)) * (k : ℝ) := by
        have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hper i)
        linarith

/-- The conditional assembly in the target shape: if the
    divisor-weighted estimate holds at every endpoint in the form
    `divWeightedErrSum ≤ Cw · Y' · log(Y')^{-A'}`, then the
    second-moment error is at most the corresponding sum of
    endpoint bounds plus `Λ·k`. Any fixed polylog factor in the
    hypothesis is absorbed by re-choosing `A'`, so none is
    carried here. -/
theorem secondMoment_divWeightedBV_bound_target {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (Cw A' : ℝ)
    (hDiv : ∀ i, divWeightedErrSum M (y + h i) (R ^ 2) k
        ≤ Cw * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A')) ∧
      divWeightedErrSum M (x + h i) (R ^ 2) k
        ≤ Cw * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A'))) :
    abs (secondMoment k h R (lamSelberg k R deg) x y
        - bvMainTerm k h R (lamSelberg k R deg) M x y)
      ≤ (∑ i, (Cw * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + Cw * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A'))))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (lamSelberg k R deg d * lamSelberg k R deg e)) * (k : ℝ) :=
  secondMoment_divWeightedBV_bound h R deg hR M hxy wit hwit
    (fun Y' => Cw * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A'))) hDiv

/-! ### What the plain BV record buys: the sup-factor bound -/

/-- The naive bound, with its exact cost: if the weight
    `τ_{k+1}(L)²` is at most `W` throughout the range and the
    unweighted max-error sum is at most `B`, then the
    divisor-weighted sum is at most `W · B`. The factor `W` is
    the whole obstruction — see the header. -/
theorem divWeightedErrSum_le_of_sum_bound {k : ℕ} (M : ℕ → ℕ → ℝ) (Y' Q : ℕ)
    {W B : ℝ} (hWnn : 0 ≤ W)
    (hw : ∀ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 2 ≤ W)
    (hsum : ∑ L ∈ Finset.range (Q + 1), maxCoprimeErr M Y' L ≤ B) :
    divWeightedErrSum M Y' Q k ≤ W * B := by
  classical
  calc divWeightedErrSum M Y' Q k
      = ∑ L ∈ Finset.range (Q + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L := rfl
    _ ≤ ∑ L ∈ Finset.range (Q + 1), W * maxCoprimeErr M Y' L :=
        Finset.sum_le_sum (fun L hL =>
          mul_le_mul_of_nonneg_right (hw L hL) (maxCoprimeErr_nonneg _ _ _))
    _ = W * ∑ L ∈ Finset.range (Q + 1), maxCoprimeErr M Y' L := by rw [Finset.mul_sum]
    _ ≤ W * B := mul_le_mul_of_nonneg_left hsum hWnn

/-- The naive bound from a platform-shaped BV sum hypothesis: at a
    height `Y'` with the level constraint, the BV sum bound `B`
    controls the unweighted max-error sum over `L ≤ R²` (the `L = 0`
    term vanishes, and every `1 ≤ L ≤ R²` lies in the BV range),
    so the divisor-weighted sum is at most `W · B` — again with
    the sup factor `W` as the obstruction. -/
theorem divWeightedErrSum_le_of_bvSumBound {k : ℕ} (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B W : ℝ) (hWnn : 0 ≤ W)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B)
    (hw : ∀ L ∈ Finset.range (R ^ 2 + 1), (tupleProdCount (k + 1) L : ℝ) ^ 2 ≤ W) :
    divWeightedErrSum M Y' (R ^ 2) k ≤ W * B := by
  classical
  apply divWeightedErrSum_le_of_sum_bound M Y' (R ^ 2) hWnn hw
  have hmax0 : maxCoprimeErr M Y' 0 = 0 := by
    have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
        (fun r => abs ((primeCountAP Y' 0 r : ℝ) - M Y' 0)))).Nonempty := by
      rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
      exact Finset.not_nonempty_empty
    unfold maxCoprimeErr
    rw [dif_neg hne0]
  have hsplit : (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L)
      = ∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => 1 ≤ L),
        maxCoprimeErr M Y' L := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (R ^ 2 + 1)) (fun L => 1 ≤ L)
      (fun L => maxCoprimeErr M Y' L)]
    have hnot : (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => ¬ 1 ≤ L),
        maxCoprimeErr M Y' L) = 0 := by
      apply Finset.sum_eq_zero
      intro L hL
      rw [Finset.mem_filter] at hL
      have hL0 : L = 0 := by omega
      rw [hL0, hmax0]
    rw [hnot, add_zero]
  rw [hsplit]
  calc (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L => 1 ≤ L), maxCoprimeErr M Y' L)
      ≤ ∑ L ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        maxCoprimeErr M Y' L := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro L hL
          rw [Finset.mem_filter, Finset.mem_range] at hL
          exact mem_bvRange_of_le_sq hL.2 (by omega) hlev
        · intro L _ _
          exact maxCoprimeErr_nonneg _ _ _
    _ ≤ B := sum_maxCoprimeErr_le_of_sum_bound M Y' _ _ hBV


/-! ### The cutoff does not factor -/

/-- The polynomial cutoff does not factor over sums: at `s₁ = s₂ = 1/2`
    and `deg ≥ 1`, the left side is `(1 - 1)^deg = 0` while the right
    side is `(1/2)^(2*deg) > 0`. This is the structural reason the
    Selberg weight has no pure Euler product: `log(D₁D₂)` adds, but
    the cutoff polynomial does not split over addition. -/
theorem cutoff_not_mul {deg : ℕ} (hdeg : 1 ≤ deg) :
    (1 - ((1 : ℝ) / 2 + (1 : ℝ) / 2)) ^ deg ≠
      (1 - (1 : ℝ) / 2) ^ deg * (1 - (1 : ℝ) / 2) ^ deg := by
  have h1 : (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 := by norm_num
  rw [h1]
  simp only [sub_self]
  rw [zero_pow (by omega : deg ≠ 0)]
  have hpos : (0 : ℝ) < (1 - (1 : ℝ) / 2) ^ deg * (1 - (1 : ℝ) / 2) ^ deg := by
    apply mul_pos <;> apply pow_pos <;> norm_num
  exact (ne_of_gt hpos).symm

/-! ### Binomial expansion of the weight -/

/-- Binomial expansion: `(1 - t)^deg = ∑_{j ≤ deg} (deg.choose j) * (-t)^j`. -/
theorem one_sub_pow_expand (t : ℝ) (deg : ℕ) :
    (1 - t) ^ deg = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (-t) ^ j := by
  have h1 : (1 - t) ^ deg = ∑ k ∈ Finset.range (deg + 1),
      (deg.choose k : ℝ) * (-t) ^ (deg - k) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, one_mul, mul_comm]
  rw [h1]
  rw [← Finset.sum_range_reflect
    (fun j => (deg.choose j : ℝ) * (-t) ^ j) (deg + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkk : k ≤ deg := by omega
  have hdeg : deg + 1 - 1 - k = deg - k := by omega
  rw [hdeg, Nat.choose_symm hkk]

/-- On the support, the Selberg weight is a finite monomial sum in
    `log D`: `λ_d = ∑_{j ≤ deg} (deg.choose j) * μ(D) * (-log D/log R)^j`. -/
theorem lamSelberg_expand {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (-(Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R)) ^ j := by
  rw [lamSelberg_eq_of_mem_support hd, one_sub_pow_expand]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ### Monomial pair sums and the expansion of singSum -/

/-- The pair sum with monomial weights: the `(a, b)`-monomial piece of
    the Selberg singular sum. The `φ(L)` denominator and the
    `goodPair` condition are exactly those of `singSum`. -/
noncomputable def monomialPairSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

/-- Four-fold sum commutation: move the monomial indices outside the
    pair sums. -/
theorem sum_comm4 {α γ : Type*} {s : Finset α} {t : Finset γ}
    (F : α → α → γ → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
  have h1 : ∀ d : α, (∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    intro d
    exact Finset.sum_comm
  have h2 : (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    calc _ = ∑ d ∈ s, ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_congr rfl (fun d _ => h1 d)
      _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_comm
  have h3 : ∀ a : γ, (∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b)
      = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
    intro a
    calc _ = ∑ d ∈ s, ∑ b ∈ t, ∑ e ∈ s, F d e a b := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
      _ = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := Finset.sum_comm
  calc _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := h2
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b :=
        Finset.sum_congr rfl (fun a _ => h3 a)

/-- The exact decomposition of the Selberg singular sum into monomial
    pair sums. This is the honest replacement for an Euler product:
    each monomial piece is a Dirichlet-type sum over good pairs, and
    its evaluation (multinomial prime expansion, Mertens-type
    estimates, local factors) is the remaining analytic core. -/
theorem singSum_selberg_expand {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
  have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) := by
    intro d hd e he
    by_cases hg : goodPair h d e i
    · rw [if_pos hg]
      rw [lamSelberg_expand hd, lamSelberg_expand he, Finset.sum_mul_sum]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [if_pos hg]
      ring
    · rw [if_neg hg]
      simp only [if_neg hg, mul_zero, Finset.sum_const_zero]
  have h2 : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0))
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
  have hfactor : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0))
      = (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
    intro a _ b _
    unfold monomialPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold singSum
  rw [h2, sum_comm4]
  exact Finset.sum_congr rfl
    (fun a ha => Finset.sum_congr rfl (fun b hb => hfactor a ha b hb))

/-! ### Squarefree restriction of the monomial sums -/

/-- A monomial summand vanishes when the first product is not
    squarefree: the Möbius factor is zero. -/
theorem monomialPairSum_summand_eq_zero_of_not_squarefree {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (a b : ℕ) (i : Fin k)
    {d e : Fin k → ℕ} (hd : ¬ Squarefree (∏ j, d j)) :
    (if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
     else 0) = 0 := by
  by_cases hg : goodPair h d e i
  · rw [if_pos hg]
    have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    rw [hmu]
    simp
  · rw [if_neg hg]

/-- Symmetric version: a monomial summand vanishes when the second
    product is not squarefree. Together with the previous lemma, every
    monomial sum is a sum over squarefree products only. -/
theorem monomialPairSum_summand_eq_zero_of_not_squarefree_right {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (a b : ℕ) (i : Fin k)
    {d e : Fin k → ℕ} (he : ¬ Squarefree (∏ j, e j)) :
    (if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
     else 0) = 0 := by
  by_cases hg : goodPair h d e i
  · rw [if_pos hg]
    have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree he
    rw [hmu]
    simp
  · rw [if_neg hg]


/-! ### Monomial sums grouped by combined modulus -/

/-- The monomial pair sum at exact combined modulus `L`: the
    `(a, b)`-monomial piece restricted to good support pairs whose
    coordinatewise-lcm modulus equals `L`. No `1/φ(L)` factor here;
    the grouping theorem supplies it outside. -/
noncomputable def monomialPairSumAtL (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
      ∧ goodPair h d e i)
    then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
    else 0

/-- The monomial sum grouped by combined modulus, mirroring
    `singSum_eq_sum_over_L`: the level bound `L ≤ R²` (from
    `lcm_le_sq_of_mem_support`) keeps the modulus range finite and
    inside the BV range. -/
theorem monomialPairSum_eq_sum_over_L {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    monomialPairSum k h R a b i
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  have hmem : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
        ∈ Finset.Icc 1 (R ^ 2) := by
    intro d hd e he
    obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨h1', -, -⟩ := mem_tupleSupport.mp he
    have hLne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 := by
      apply Finset.lcm_ne_zero_iff.mpr
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := h1 j
        omega
      · have hj := h1' j
        omega
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hLne, lcm_le_sq_of_mem_support hd he⟩
  have hstep1 : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then
        (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) := by
    intro d hd e he
    rw [Finset.sum_ite_eq', if_pos (hmem d hd e he)]
  have hstep3 : ∀ L ∈ Finset.Icc 1 (R ^ 2),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0))
      = (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
    intro L _
    have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0)
        = (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
      intro d _ e _
      by_cases hLe : L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      · by_cases hg : goodPair h d e i
        · rw [if_pos hLe, if_pos hg, if_pos ⟨hLe.symm, hg⟩,
            mul_comm (1 / ((Nat.totient L : ℕ) : ℝ)) _, mul_one_div]
        · rw [if_pos hLe, if_neg hg, if_neg (fun hcon => hg hcon.2), mul_zero]
      · rw [if_neg hLe, if_neg (fun hcon => hLe hcon.1.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))]
    unfold monomialPairSumAtL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold monomialPairSum
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hstep1 d hd e he))]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl (fun L hL => hstep3 L hL)

/-- The Selberg singular sum in fully grouped form: binomial
    coefficients times the modulus-grouped monomial sums. This is the
    exact identity the Mertens-type evaluation starts from. -/
theorem singSum_selberg_grouped {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  rw [singSum_selberg_expand]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [monomialPairSum_eq_sum_over_L]

/-! ### Lcms of squarefree numbers are squarefree -/

/-- The lcm of two squarefree numbers is squarefree, via
    factorization: the factorization of the lcm is the pointwise max
    of the factorizations, each `≤ 1`. -/
theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (Squarefree.natFactorization_le_one p ha)
    (Squarefree.natFactorization_le_one p hb)

/-- The lcm of a finite family of squarefree numbers is squarefree,
    via `Finset.factorization_lcm`: the factorization of the lcm is
    the finset sup of the factorizations, each `≤ 1`. -/
theorem squarefree_finset_lcm {ι : Type*} {s : Finset ι} {g : ι → ℕ}
    (h0 : ∀ j ∈ s, g j ≠ 0) (hsq : ∀ j ∈ s, Squarefree (g j)) :
    Squarefree (s.lcm g) := by
  apply Nat.squarefree_of_factorization_le_one (Finset.lcm_ne_zero_iff.mpr h0)
  intro p
  rw [Finset.factorization_lcm h0 p]
  apply Finset.sup_le
  intro j hj
  exact Squarefree.natFactorization_le_one p (hsq j hj)

/-- The pair sum at modulus `L` vanishes unless `L` is squarefree:
    a non-squarefree combined modulus forces some coordinate lcm to
    be non-squarefree (contrapositive of `squarefree_finset_lcm`),
    hence some coordinate, hence some product, to be non-squarefree,
    killing the Möbius factor. So the grouped sum is a sum over
    squarefree moduli only. -/
theorem monomialPairSumAtL_eq_zero_of_not_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) {L : ℕ} (hL : ¬ Squarefree L) :
    monomialPairSumAtL k h R a b i L = 0 := by
  unfold monomialPairSumAtL
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  by_cases hcon : (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
    ∧ goodPair h d e i)
  · rw [if_pos hcon]
    obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp he
    have hLnsq : ¬ Squarefree (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by
      rw [hcon.1]
      exact hL
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin k)), Nat.lcm (d j) (e j) ≠ 0 := by
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := hd1 j
        omega
      · have hj := he1 j
        omega
    have hex : ∃ j, ¬ Squarefree (Nat.lcm (d j) (e j)) := by
      by_contra hnone
      push Not at hnone
      exact hLnsq (squarefree_finset_lcm h0 (fun j _ => hnone j))
    obtain ⟨j, hj⟩ := hex
    by_cases hdjsq : Squarefree (d j)
    · have hejsq : ¬ Squarefree (e j) := fun hh => hj (squarefree_lcm hdjsq hh)
      have hE : ¬ Squarefree (∏ j, e j) := fun hsq =>
        hejsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => e j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hE
      rw [hmu]
      simp
    · have hD : ¬ Squarefree (∏ j, d j) := fun hsq =>
        hdjsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => d j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
      rw [hmu]
      simp
  · rw [if_neg hcon]



/-! ### The finite local-factor identity -/

/-- The local-factor identity for an arithmetic function: for `f`
    multiplicative and `n` squarefree, the divisor sum of `μ · f`
    factors as a product over the prime divisors of `n`. This is
    Mathlib's `prodPrimeFactors_one_sub_of_squarefree`, with the
    Möbius cast written in the exact form the monomial sums use
    (the cast application is definitionally the cast value, by
    `ArithmeticFunction.intCoe_apply`). -/
theorem sum_mu_mul_eq_prod_of_squarefree {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d
      = ∏ p ∈ n.primeFactors, (1 - f p) := by
  have key := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hn
  rw [key]

/-- The local-factor identity for a plain multiplicative function
    `F` with `F 1 = 1`: apply the arithmetic-function version to
    the zero-hom that agrees with `F` away from `0` (every divisor
    and every prime factor is nonzero). -/
theorem sum_mu_mul_fun_eq_prod_of_squarefree {F : ℕ → ℝ} (hF1 : F 1 = 1)
    (hFmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * F d
      = ∏ p ∈ n.primeFactors, (1 - F p) := by
  let f : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else F d, by simp⟩
  have hf1 : f 1 = 1 := by
    show (if (1 : ℕ) = 0 then (0 : ℝ) else F 1) = 1
    rw [if_neg one_ne_zero]
    exact hF1
  have hfmult : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨hf1, ?_⟩
    intro m n hm hn hmn
    show (if m * n = 0 then (0 : ℝ) else F (m * n))
      = (if m = 0 then (0 : ℝ) else F m) * (if n = 0 then (0 : ℝ) else F n)
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    exact hFmul hmn
  have hfd : ∀ d ∈ n.divisors, f d = F d := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rcases Nat.mem_divisors.mp hd with ⟨hdvd, -⟩
      intro h
      rw [h] at hdvd
      exact hn.ne_zero (by simpa using hdvd)
    show (if d = 0 then (0 : ℝ) else F d) = F d
    rw [if_neg hd0]
  have hfp : ∀ p ∈ n.primeFactors, f p = F p := by
    intro p hp
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    show (if p = 0 then (0 : ℝ) else F p) = F p
    rw [if_neg hp0]
  calc ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * F d
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d :=
        Finset.sum_congr rfl (fun d hd => by rw [hfd d hd])
    _ = ∏ p ∈ n.primeFactors, (1 - f p) :=
        sum_mu_mul_eq_prod_of_squarefree hfmult hn
    _ = ∏ p ∈ n.primeFactors, (1 - F p) :=
        Finset.prod_congr rfl (fun p hp => by rw [hfp p hp])


/-! ### Summation by parts -/

/-- Summation by parts for real sequences: a weighted sum is its
    partial sum times the last weight, minus the sum of partial sums
    times weight differences. This is the discrete engine that turns
    μ-weighted log-power sums into partial-sum form, where
    Mertens-type estimates plug in. Proved by induction on `n`. -/
theorem abel_sum (a f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1), a i * f i
      = (∑ i ∈ Finset.range (n + 1), a i) * f n
        - ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Finset.sum_range_succ (fun i => a i * f i) (n + 1)
    have h2 := Finset.sum_range_succ (fun i => a i) (n + 1)
    have h3 := Finset.sum_range_succ
      (fun i => (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i)) n
    rw [h1, h2, h3, ih]
    ring

/-! ### The deg-integral in closed form -/

/-- The deg-integral in closed form: `∫ x in 0..1, (1 - x)^m =
    1 / (m + 1)`, by the reflection substitution plus
    `integral_pow`. -/
theorem integral_one_sub_pow (m : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ m = 1 / ((m : ℝ) + 1) := by
  have h := intervalIntegral.integral_comp_sub_mul (f := fun t : ℝ => t ^ m)
    (a := (0 : ℝ)) (b := (1 : ℝ)) (c := (1 : ℝ)) one_ne_zero (d := (1 : ℝ))
  simp only [one_mul, sub_self, sub_zero, inv_one, one_smul] at h
  rw [h, integral_pow]
  simp only [one_pow, zero_pow (show m + 1 ≠ 0 by omega), sub_zero]


/-! ### Admissibility and the singular series -/

/-- The number of residue classes of `h` mod `p`: `ω_p(h)`. -/
def residueCount {k : ℕ} (h : Fin k → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ.image (fun i => h i % p)).card

/-- Admissibility of the tuple `h`: at every prime `p`, the shifts
    do not cover all residue classes mod `p`. Stated in the form
    `ω_p(h) < p` for all `p`, as an explicit hypothesis wherever it
    is needed — never an ambient assumption. -/
def Admissible {k : ℕ} (h : Fin k → ℕ) : Prop :=
  ∀ p, Nat.Prime p → residueCount h p < p

/-- The local factor at `p` for a `k`-tuple:
    `(1 - ω_p(h)/p) / (1 - 1/p)^k`. -/
noncomputable def localFactor {k : ℕ} (h : Fin k → ℕ) (p : ℕ) : ℝ :=
  (1 - (residueCount h p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ k

/-- The truncated singular series: the product of local factors
    over primes `≤ P`. The full series is the limit of these
    truncations; convergence (which needs admissibility) is part of
    the remaining evaluation, not assumed here. -/
noncomputable def singSeriesTrunc {k : ℕ} (h : Fin k → ℕ) (P : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (P + 1)).filter Nat.Prime, localFactor h p


/-! ### The per-modulus monomial piece is τ²-bounded -/

/-- The per-modulus monomial piece is bounded by the fiber count:
    every surviving term has `|μ| ≤ 1` and log-ratio at most `1`
    in absolute value on the support, and the non-squarefree terms
    vanish. -/
theorem monomialPairSumAtL_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) (hR : 2 ≤ R) :
    abs (monomialPairSumAtL k h R a b i L) ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
  classical
  have hlog : ∀ d ∈ tupleSupport k R,
      abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ≤ 1 := by
    intro d hd
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hd
    have hD1 : 1 ≤ ∏ j, d j := Finset.one_le_prod' (fun j _ => h1 j)
    have hDpos : (0 : ℝ) < ((∏ j, d j : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hD1)
    have hlogR : (0 : ℝ) < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    have hnn : (0 : ℝ) ≤ Real.log ((∏ j, d j : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hD1)
    have hle : Real.log ((∏ j, d j : ℕ) : ℝ) ≤ Real.log (R : ℝ) :=
      Real.log_le_log hDpos (by exact_mod_cast h3)
    have hfrac0 : (0 : ℝ) ≤ Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log (R : ℝ) :=
      div_nonneg hnn hlogR.le
    have hfrac1 : Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log (R : ℝ) ≤ 1 :=
      (div_le_one hlogR).mpr hle
    rw [abs_neg, abs_of_nonneg hfrac0]
    exact hfrac1
  have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ goodPair h d e i)
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        else 0)
      ≤ (if goodPair h d e i
          ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
        then (1 : ℝ) else 0) := by
    intro d hd e he
    by_cases hfib : goodPair h d e i
        ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
        ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
    · rw [if_pos hfib]
      obtain ⟨hgood, hlcm, -, -⟩ := hfib
      rw [if_pos ⟨hlcm, hgood⟩]
      have hmuD : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ)) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hmuE : abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ)) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hlogD : abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ≤ 1 :=
        hlog d hd
      have hlogE : abs (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ≤ 1 :=
        hlog e he
      have hp1 : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
          * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ)) ≤ 1 := by
        calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
            ≤ 1 * 1 := mul_le_mul hmuD hmuE (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hp2 : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
          * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
          * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a ≤ 1 := by
        calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
              * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a
            ≤ 1 * 1 := mul_le_mul hp1 (pow_le_one₀ (abs_nonneg _) hlogD)
              (pow_nonneg (abs_nonneg _) _) zero_le_one
          _ = 1 := one_mul 1
      calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b)
          = abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
              * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a
              * (abs (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R))) ^ b := by
            simp only [abs_mul, abs_pow]
        _ ≤ 1 * 1 := mul_le_mul hp2 (pow_le_one₀ (abs_nonneg _) hlogE)
            (pow_nonneg (abs_nonneg _) _) zero_le_one
        _ = 1 := one_mul 1
    · rw [if_neg hfib]
      by_cases hatl : (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ goodPair h d e i)
      · rw [if_pos hatl]
        have hnsq : ¬ Squarefree (∏ j, d j) ∨ ¬ Squarefree (∏ j, e j) := by
          by_contra hc
          push Not at hc
          exact hfib ⟨hatl.2, hatl.1, hc.1, hc.2⟩
        rcases hnsq with hD | hE
        · have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
            exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
          rw [hmu]
          simp
        · have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
            exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hE
          rw [hmu]
          simp
      · rw [if_neg hatl]
        simp
  have step1 : abs (monomialPairSumAtL k h R a b i L)
      ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
    unfold monomialPairSumAtL
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _))
  have step2 : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      ≤ (fiberCountSelberg h R i L : ℝ) := by
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                ∧ goodPair h d e i)
              then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                  * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                  * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                  * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              else 0))
        ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            (if goodPair h d e i
                ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
              then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hterm d hd e he))
      _ = (fiberCountSelberg h R i L : ℝ) := by
          rw [← Finset.sum_product', Finset.sum_boole]
          rfl
  have hcard : (fiberCountSelberg h R i L : ℝ)
      ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
    exact_mod_cast fiberCountSelberg_le h R i L
  exact le_trans (le_trans step1 step2) hcard

/-- The whole monomial sum is bounded by the finite τ²-sum over the
    modulus range (using `1/φ(L) ≤ 1` for `L ≥ 1`). -/
theorem monomialPairSum_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (hR : 2 ≤ R) :
    abs (monomialPairSum k h R a b i)
      ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2), (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
  rw [monomialPairSum_eq_sum_over_L]
  calc abs (∑ L ∈ Finset.Icc 1 (R ^ 2),
          (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L)
      ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2),
          abs ((1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2), (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro L hL
        rw [Finset.mem_Icc] at hL
        have hφpos : (0 : ℝ) < ((Nat.totient L : ℕ) : ℝ) := by
          exact_mod_cast (Nat.totient_pos.mpr (show 0 < L by omega))
        have hφ0 : (0 : ℝ) ≤ 1 / ((Nat.totient L : ℕ) : ℝ) :=
          div_nonneg zero_le_one hφpos.le
        have hφ1 : 1 / ((Nat.totient L : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hφpos]
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (Nat.totient_pos.mpr (show 0 < L by omega)).ne')
        rw [abs_mul, abs_of_nonneg hφ0]
        calc (1 / ((Nat.totient L : ℕ) : ℝ)) * abs (monomialPairSumAtL k h R a b i L)
            ≤ 1 * (tupleProdCount (k + 1) L : ℝ) ^ 2 :=
              mul_le_mul hφ1 (monomialPairSumAtL_abs_le h R a b i L hR)
                (abs_nonneg _) zero_le_one
          _ = (tupleProdCount (k + 1) L : ℝ) ^ 2 := one_mul _

/-! ### The grouped form over squarefree moduli only -/

/-- The Selberg singular sum, grouped over squarefree moduli only:
    the non-squarefree pieces vanish, so the evaluation only ever
    sees `L` squarefree — where `combined_lcm_eq` applies. -/
theorem singSum_selberg_grouped_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  rw [singSum_selberg_grouped]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hinner : (∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L)
      = ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro L hL hnf
    have hnsq : ¬ Squarefree L := by
      intro hsq
      exact hnf (Finset.mem_filter.mpr ⟨hL, hsq⟩)
    rw [monomialPairSumAtL_eq_zero_of_not_squarefree h R a b i hnsq]
    simp
  rw [hinner]

/-! ### Regrouping by products: isolating the good count -/

/-- The good-pair count at fixed products and modulus: the number
    of support pairs `(d, e)` with `∏ d = D`, `∏ e = E`, good at
    `i`, and coordinatewise-lcm modulus `L`. This is the single
    object whose local evaluation is still missing (see the header:
    gap piece (1)). -/
noncomputable def goodCountAtL {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k)
    (D E L : ℕ) : ℕ :=
  ((tupleSupport k R ×ˢ tupleSupport k R).filter
    (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)).card

/-- Regrouping of the per-modulus monomial piece by products: the
    μ/log-power factor depends only on `(D, E)`, so it factors out
    of the fiber sum, leaving exactly `goodCountAtL`. -/
theorem monomialPairSumAtL_eq_goodCount_sum {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) :
    monomialPairSumAtL k h R a b i L
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) := by
  classical
  have hmaps : ∀ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
      (∏ j, p.1 j, ∏ j, p.2 j) ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hp1
    obtain ⟨h1', -, h3'⟩ := mem_tupleSupport.mp hp2
    rw [Finset.mem_product]
    change (∏ j, p.1 j) ∈ Finset.Icc 1 R ∧ (∏ j, p.2 j) ∈ Finset.Icc 1 R
    constructor <;> rw [Finset.mem_Icc]
    · exact ⟨Finset.one_le_prod' (fun j _ => h1 j), h3⟩
    · exact ⟨Finset.one_le_prod' (fun j _ => h1' j), h3'⟩
  have hfib : (∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  have hinner : ∀ D ∈ Finset.Icc 1 R, ∀ E ∈ Finset.Icc 1 R,
      (∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      = (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) := by
    intro D _ E _
    have hfilter : (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E))
        = (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E) := by
      apply Finset.filter_congr
      intro p _
      simp [Prod.mk.injEq]
    rw [hfilter]
    have hterm : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0)
        = (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
            * (-(Real.log (D : ℝ) / Real.log R)) ^ a
            * (-(Real.log (E : ℝ) / Real.log R)) ^ b
            * (if goodPair h p.1 p.2 i
                ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
              then (1 : ℝ) else 0) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨-, hD, hE⟩ := hp
      by_cases hcond : goodPair h p.1 p.2 i
          ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
      · rw [if_pos hcond, if_pos ⟨hcond.2, hcond.1⟩, hD, hE]
        ring
      · rw [if_neg hcond, if_neg (fun hcon => hcond ⟨hcon.2, hcon.1⟩)]
        simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_boole]
    congr 1
    have hcard : ((tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E)).filter
          (fun p => goodPair h p.1 p.2 i
            ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)
        = (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      simp only [and_assoc]
    rw [hcard]
    rfl
  calc monomialPairSumAtL k h R a b i L
      = ∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
        unfold monomialPairSumAtL
        exact (Finset.sum_product' (s := tupleSupport k R) (t := tupleSupport k R)
          (f := fun d e => if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
              ∧ goodPair h d e i)
            then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            else 0)).symm
    _ = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := hfib
    _ = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) :=
        Finset.sum_congr rfl (fun D hD => Finset.sum_congr rfl (fun E hE => hinner D hD E hE))

/-! ### The one-variable Mertens sums and their Abel form -/

/-- The μ²/φ weight at `D`: `μ(D)²/φ(D)` on squarefree `D`, `0`
    otherwise (the square of the Möbius value is the squarefree
    indicator). -/
noncomputable def mertensWeight (D : ℕ) : ℝ :=
  if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
    / ((Nat.totient D : ℕ) : ℝ) else 0

/-- The one-variable μ²/φ-type log-power sum: `∑_{D ≤ T}
    μ²(D)/φ(D) · (log D)^m`, in range form so `abel_sum` applies
    directly. -/
noncomputable def mertensMuSqSum (m : ℕ) (T : ℕ) : ℝ :=
  ∑ D ∈ Finset.range (T + 1), mertensWeight D * (Real.log (D : ℝ)) ^ m

/-- Abel transform of the Mertens sum into partial-sum form: the
    form in which Mertens-type estimates plug in (they bound the
    partial sums `∑_{D ≤ i} μ²(D)/φ(D)`; Abel converts). -/
theorem mertensMuSqSum_abel (m : ℕ) (T : ℕ) :
    mertensMuSqSum m T
      = (∑ D ∈ Finset.range (T + 1), mertensWeight D) * (Real.log (T : ℝ)) ^ m
        - ∑ i ∈ Finset.range T,
            (∑ D ∈ Finset.range (i + 1), mertensWeight D)
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
  unfold mertensMuSqSum
  exact abel_sum mertensWeight (fun D => (Real.log (D : ℝ)) ^ m) T

/-- Specification of the exact Mertens-type input still needed
    (gap piece (2) in the header): the μ²/φ log-power sum is a
    constant `C m` times `(log T)^(m+1)`, up to an explicit error
    `err m T`. The constant function `C` is a parameter here —
    its exact value (from the local Euler factors) is part of what
    the Mertens pass must establish, and is NOT asserted by this
    definition. -/
def MertensMuSqBound (C : ℕ → ℝ) (err : ℕ → ℕ → ℝ) : Prop :=
  ∀ m T, abs (mertensMuSqSum m T - C m * (Real.log (T : ℝ)) ^ (m + 1)) ≤ err m T

/-! ### Conditional assembly: from per-monomial evaluations to singSum -/

/-- Conditional evaluation of the Selberg singular sum from
    per-monomial evaluations: if each monomial piece is `mainMono`
    up to `errMono`, then `singSum` is the binomial combination of
    the main terms up to the binomial combination of the errors.
    The hypothesis `hMono` is exactly the per-monomial Mertens
    evaluation whose proof needs gap pieces (1) and (2); this
    theorem is the assembly step only. -/
theorem singSum_selberg_cond_eval {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) (mainMono : ℕ → ℕ → ℝ) (errMono : ℕ → ℕ → ℝ)
    (hMono : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs (monomialPairSum k h R a b i - mainMono a b) ≤ errMono a b) :
    abs (singSum k h R (lamSelberg k R deg) i
        - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono a b)
      ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono a b := by
  rw [singSum_selberg_expand]
  have hsub : (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i)
      - (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono a b)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ)
          * (monomialPairSum k h R a b i - mainMono a b) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hsub]
  calc abs (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ)
            * (monomialPairSum k h R a b i - mainMono a b))
      ≤ ∑ a ∈ Finset.range (deg + 1),
          abs (∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ)
              * (monomialPairSum k h R a b i - mainMono a b)) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          abs ((deg.choose a : ℝ) * (deg.choose b : ℝ)
            * (monomialPairSum k h R a b i - mainMono a b)) :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono a b := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        have hca : (0 : ℝ) ≤ (deg.choose a : ℝ) := Nat.cast_nonneg _
        have hcb : (0 : ℝ) ≤ (deg.choose b : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hca, abs_of_nonneg hcb]
        exact mul_le_mul_of_nonneg_left (hMono a ha b hb) (mul_nonneg hca hcb)


/-! ### The conditional assembly -/

/-- Conditional GPY assembly for the Selberg weight. IF every
    monomial piece is evaluated by `mainMono` up to `errMono`
    (hypothesis `hMono`, exactly as in
    `singSum_selberg_cond_eval`, here with `mainMono`/`errMono`
    allowed to depend on the coordinate `i`), AND the
    divisor-weighted BV estimate holds at every interval endpoint
    for the model `li/φ` (hypothesis `hDiv`, exactly as in
    `secondMoment_divWeightedBV_bound`, with `M = li/φ`), THEN
    the second moment equals its monomial-evaluated main term —
    the coordinate sum of li-differences times the binomial
    combination of the monomial main terms — up to an error with
    exactly three pieces: the `hDiv` endpoint terms, the `Λ·k`
    fiber term, and the `hMono` terms weighted by the
    li-differences. The standing hypotheses are those of the two
    inputs: `2 ≤ R`, `x ≤ y`, and the grouped-bound witness
    hypotheses. -/
theorem secondMoment_assembly_cond {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (li : ℝ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, goodPair h d e i →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (mainMono errMono : Fin k → ℕ → ℕ → ℝ)
    (E : ℕ → ℝ)
    (hMono : ∀ i, ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs (monomialPairSum k h R a b i - mainMono i a b) ≤ errMono i a b)
    (hDiv : ∀ i, divWeightedErrSum (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ))
        (y + h i) (R ^ 2) k ≤ E (y + h i) ∧
      divWeightedErrSum (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ))
        (x + h i) (R ^ 2) k ≤ E (x + h i)) :
    abs (secondMoment k h R (lamSelberg k R deg) x y
        - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (lamSelberg k R deg d * lamSelberg k R deg e)) * (k : ℝ)
        + ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) := by
  classical
  -- Error side: the divisor-weighted bound, instantiated at M = li/φ.
  have hS2 := secondMoment_divWeightedBV_bound h R deg hR
    (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) hxy wit hwit E hDiv
  -- The meeting point: bvMainTerm (li/φ) factors through singSum.
  have hfact := bvMainTerm_li_div_totient h R (lamSelberg k R deg) li (x := x) (y := y)
  -- Monomial side, per coordinate.
  have hmono_i : ∀ i, abs (singSum k h R (lamSelberg k R deg) i
        - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b)
      ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b :=
    fun i => singSum_selberg_cond_eval h R deg i (mainMono i) (errMono i) (hMono i)
  -- The main-term comparison: replacing singSum by its evaluated form
  -- costs the li-difference-weighted monomial errors.
  have hmain : abs (bvMainTerm k h R (lamSelberg k R deg)
        (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) x y
        - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
      ≤ ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
          (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) := by
    rw [hfact]
    have hsub : (∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
          * singSum k h R (lamSelberg k R deg) i)
        - (∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
        = ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (singSum k h R (lamSelberg k R deg) i
              - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
                  (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [mul_sub])
    rw [hsub]
    calc abs (∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (singSum k h R (lamSelberg k R deg) i
              - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
                  (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
        ≤ ∑ i, abs ((li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (singSum k h R (lamSelberg k R deg) i
              - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
                  (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b)) :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            abs (singSum k h R (lamSelberg k R deg) i
              - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
                  (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b) :=
          Finset.sum_congr rfl (fun i _ => abs_mul _ _)
      _ ≤ ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hmono_i i) (abs_nonneg _))
  -- Triangle inequality over the BV main term.
  have hsplit : secondMoment k h R (lamSelberg k R deg) x y
        - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b)
      = (secondMoment k h R (lamSelberg k R deg) x y
          - bvMainTerm k h R (lamSelberg k R deg)
              (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) x y)
        + (bvMainTerm k h R (lamSelberg k R deg)
              (fun Y L => li (Y : ℝ) / ((Nat.totient L : ℕ) : ℝ)) x y
          - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
              (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
                (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b)) := by
        ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (by linarith [hS2, hmain])

theorem secondMoment_assembly_cond_restated_pub2 {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (li : ℝ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (mainMono errMono : Fin k → ℕ → ℕ → ℝ)
    (E : ℕ → ℝ)
    (hMono : ∀ i, ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs ((∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
        else 0) - mainMono i a b) ≤ errMono i a b)
    (hDiv : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (y + h i) ∧
      (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (x + h i)) :
    abs ((∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0)
            else 0) ^ 2)
      - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          abs ((if ∏ i, d i ≤ R then
                (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                  * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)
              * (if ∏ i, e i ≤ R then
                (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                  * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0))) * (k : ℝ)
        + ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) := by
  have hmain := secondMoment_assembly_cond h R deg hR li hxy wit hwit mainMono errMono E hMono hDiv
  -- Only the definitions occurring in the conclusion need unfolding here:
  -- the unfolded hypotheses hMono / hDiv / hwit are already accepted by
  -- definitional equality when applying the original theorem above.
  unfold secondMoment weight primeInd tupleSupport lamSelberg at hmain
  exact hmain

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (li : ℝ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (mainMono errMono : Fin k → ℕ → ℕ → ℝ)
    (E : ℕ → ℝ)
    (hMono : ∀ i, ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs ((∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
        else 0) - mainMono i a b) ≤ errMono i a b)
    (hDiv : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (y + h i) ∧
      (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (x + h i)) :
    abs ((∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0)
            else 0) ^ 2)
      - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          abs ((if ∏ i, d i ≤ R then
                (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                  * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)
              * (if ∏ i, e i ≤ R then
                (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                  * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0))) * (k : ℝ)
        + ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) := GPY.secondMoment_assembly_cond_restated_pub2 h R deg hR li hxy wit hwit mainMono errMono E hMono hDiv
