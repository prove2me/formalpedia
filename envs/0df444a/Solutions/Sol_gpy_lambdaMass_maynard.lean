-- Prove2me | solution 1 for gpy_lambdaMass_maynard
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T21:43:32.367098+00:00
-- url     : https://prove2.me/submissions/ef76b3f4-6fe6-4a23-8091-7de1d5f14022

/-
  Submission file for the Prove2Me problem `gpy_lambdaMass_maynard` (Maynard weights: lambda-mass bound).

  Self-contained: imports Mathlib only. Contains the verified bodies of
  GPYWeights.lean, GPYCount.lean, GPYMainTerm.lean, GPYSecondMoment.lean,
  GPYBV.lean, GPYLambdaMaynard.lean, and GPYLambdaMaynardRestated.lean,
  with top-level `theorem solution` in the problem's exact binder/statement
  form (statement mechanically extracted from the restated theorem, so the
  two are textually identical). Supporting theorems (support/vanishing,
  |lambda| <= 1, and the other Maynard lemmas) are included as bodies,
  not as separate problems. No sorry tactic, no axioms beyond the
  standard ones, no platform imports.
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



/-! ### The polynomial simplex cutoff -/

/-- The polynomial simplex cutoff: F_m(t) = (1 - ∑ tᵢ)^m on the simplex
    ∑ tᵢ ≤ 1, and 0 outside. The tractable polynomial subcase of
    Maynard's smooth cutoff F. -/
noncomputable def maynardCutoff (m : ℕ) {k : ℕ} (t : Fin k → ℝ) : ℝ :=
  if ∑ i, t i ≤ 1 then (1 - ∑ i, t i) ^ m else 0

theorem maynardCutoff_nonneg (m : ℕ) {k : ℕ} (t : Fin k → ℝ) :
    0 ≤ maynardCutoff m t := by
  unfold maynardCutoff
  by_cases h : ∑ i, t i ≤ 1
  · rw [if_pos h]
    exact pow_nonneg (by linarith) m
  · rw [if_neg h]

/-- On the nonneg orthant (which is where the cutoff is ever evaluated:
    log dᵢ / log R ≥ 0), the cutoff is at most 1. The hypothesis is
    needed: for ∑ tᵢ < 0 the polynomial (1 - ∑ tᵢ)^m can exceed 1. -/
theorem maynardCutoff_le_one (m : ℕ) {k : ℕ} {t : Fin k → ℝ}
    (h0 : 0 ≤ ∑ i, t i) : maynardCutoff m t ≤ 1 := by
  unfold maynardCutoff
  by_cases h : ∑ i, t i ≤ 1
  · rw [if_pos h]
    exact pow_le_one₀ (by linarith) (by linarith)
  · rw [if_neg h]
    exact zero_le_one

theorem maynardCutoff_eq_zero_of_one_lt_sum (m : ℕ) {k : ℕ} {t : Fin k → ℝ}
    (h : 1 < ∑ i, t i) : maynardCutoff m t = 0 := by
  unfold maynardCutoff
  rw [if_neg (not_le.mpr h)]

/-! ### The Maynard–Tao weights -/

/-- The log-ratio coordinates of a tuple are always nonnegative: for
    n = 0 the logarithm is 0, and for n ≥ 1 both logarithms are
    nonnegative (with the degenerate R = 0 case giving 0/0 = 0). -/
theorem logDiv_nonneg (n R : ℕ) : 0 ≤ Real.log n / Real.log R := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    by_cases hR : R = 0
    · simp [hR]
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn1))
        (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hR))

/-- Maynard–Tao weights, polynomial subcase: λ_d = (∏ᵢ μ(dᵢ)) ·
    F_m(log d₁/log R, …, log d_k/log R). -/
noncomputable def maynardLambda (m R : ℕ) {k : ℕ} (d : Fin k → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
    maynardCutoff m (fun i => Real.log (d i) / Real.log R)

/-- A non-squarefree coordinate kills the weight (μ vanishes there). -/
theorem maynardLambda_eq_zero_of_not_squarefree (m R : ℕ) {k : ℕ}
    {d : Fin k → ℕ} (h : ∃ i, ¬ Squarefree (d i)) :
    maynardLambda m R d = 0 := by
  obtain ⟨i, hi⟩ := h
  have hmu : (ArithmeticFunction.moebius (d i) : ℝ) = 0 := by
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi]
  unfold maynardLambda
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hmu, zero_mul]

/-- Outside the simplex the cutoff — hence the weight — vanishes. -/
theorem maynardLambda_eq_zero_of_one_lt_logSum (m R : ℕ) {k : ℕ}
    {d : Fin k → ℕ}
    (h : 1 < ∑ i, Real.log (d i) / Real.log R) :
    maynardLambda m R d = 0 := by
  unfold maynardLambda
  rw [maynardCutoff_eq_zero_of_one_lt_sum m h, mul_zero]

/-- Nonzero weights live on squarefree simplex tuples: the structural
    input to any singular-series computation for this λ. -/
theorem maynardLambda_ne_zero_imp (m R : ℕ) {k : ℕ} {d : Fin k → ℕ}
    (h : maynardLambda m R d ≠ 0) :
    (∀ i, Squarefree (d i)) ∧ ∑ i, Real.log (d i) / Real.log R ≤ 1 := by
  constructor
  · by_contra hns
    push_neg at hns
    exact h (maynardLambda_eq_zero_of_not_squarefree m R hns)
  · by_contra hle
    push_neg at hle
    exact h (maynardLambda_eq_zero_of_one_lt_logSum m R hle)

/-- Uniform bound: every Maynard weight is at most 1 in absolute value
    (μ contributes at most 1 per coordinate, the cutoff at most 1). -/
theorem abs_maynardLambda_le_one (m R : ℕ) {k : ℕ} (d : Fin k → ℕ) :
    abs (maynardLambda m R d) ≤ 1 := by
  have hmu : abs (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intro i _
      exact abs_nonneg _
    · intro i _
      have h := ArithmeticFunction.abs_moebius_le_one (n := d i)
      have h2 : ((abs (ArithmeticFunction.moebius (d i)) : ℤ) : ℝ) ≤ 1 := by
        exact_mod_cast h
      rwa [Int.cast_abs] at h2
  have hF : abs (maynardCutoff m (fun i => Real.log (d i) / Real.log R)) ≤ 1 := by
    rw [abs_of_nonneg (maynardCutoff_nonneg m _)]
    apply maynardCutoff_le_one
    exact Finset.sum_nonneg (fun i _ => logDiv_nonneg (d i) R)
  unfold maynardLambda
  rw [abs_mul]
  have hprod := mul_le_mul hmu hF (abs_nonneg _) zero_le_one
  simpa using hprod

/-- Normalization sanity check: the weight at the all-ones tuple is 1
    (μ(1) = 1, log 1 = 0, F_m(0) = 1). -/
theorem maynardLambda_one (m R : ℕ) {k : ℕ} :
    maynardLambda m R (fun _ : Fin k => 1) = 1 := by
  unfold maynardLambda maynardCutoff
  simp

/-- Euler-product seed: the μ-part of the weight is multiplicative
    across coordinatewise-coprime tuples. The F-part does NOT factor
    over primes — that is exactly why the singular-series evaluation
    must go through the sum→integral approximation rather than pure
    algebra (see the header). -/
theorem moebius_prod_mul_of_coprime {k : ℕ} {d e : Fin k → ℕ}
    (h : ∀ i, Nat.Coprime (d i) (e i)) :
    (∏ i, (ArithmeticFunction.moebius (d i * e i) : ℝ))
      = (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
        (∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hmul : ArithmeticFunction.moebius (d i * e i)
      = ArithmeticFunction.moebius (d i) * ArithmeticFunction.moebius (e i) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (h i)
  rw [hmul]
  exact Int.cast_mul _ _

/-! ### The Λ-mass bound -/

/-- The λ-mass factors as the square of the ℓ¹ mass (diagonal form). -/
theorem maynardLambdaMass_eq (m R : ℕ) {k : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      abs (maynardLambda m R d * maynardLambda m R e))
      = (∑ d ∈ tupleSupport k R, abs (maynardLambda m R d)) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun d _ =>
    Finset.sum_congr rfl (fun e _ => abs_mul _ _))

/-- The ℓ¹ mass is at most the support size (each |λ_d| ≤ 1). -/
theorem sum_abs_maynardLambda_le_card (m R : ℕ) {k : ℕ} :
    (∑ d ∈ tupleSupport k R, abs (maynardLambda m R d))
      ≤ ((tupleSupport k R).card : ℝ) := by
  calc (∑ d ∈ tupleSupport k R, abs (maynardLambda m R d))
      ≤ ∑ _d ∈ tupleSupport k R, (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => abs_maynardLambda_le_one m R d)
    _ = ((tupleSupport k R).card : ℝ) := by simp

/-- The support has at most R^k tuples (it sits inside the full
    k-fold product of [1, R]). -/
theorem card_tupleSupport_le (k R : ℕ) :
    (tupleSupport k R).card ≤ R ^ k := by
  calc (tupleSupport k R).card
      ≤ ((Fintype.piFinset (fun _ => Finset.Icc 1 R))).card := by
        unfold tupleSupport
        exact Finset.card_filter_le _ _
    _ = R ^ k := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        simp [Nat.card_Icc]

/-- Combined Λ bound: Λ ≤ (R^k)². The per-term bound |λ_d| ≤ 1 is
    sharp; the final counting step card ≤ R^k is NOT — the τ-weighted
    refinement replacing it is open (see the header). -/
theorem maynardLambdaMass_le (m R : ℕ) {k : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      abs (maynardLambda m R d * maynardLambda m R e))
      ≤ ((R : ℝ) ^ k) ^ 2 := by
  rw [maynardLambdaMass_eq]
  have h1 : (∑ d ∈ tupleSupport k R, abs (maynardLambda m R d))
      ≤ ((tupleSupport k R).card : ℝ) :=
    sum_abs_maynardLambda_le_card m R
  have h2 : ((tupleSupport k R).card : ℝ) ≤ (R : ℝ) ^ k := by
    rw [← Nat.cast_pow]
    exact_mod_cast card_tupleSupport_le k R
  calc (∑ d ∈ tupleSupport k R, abs (maynardLambda m R d)) ^ 2
      ≤ (((tupleSupport k R).card : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => abs_nonneg _)) h1 2
    _ ≤ ((R : ℝ) ^ k) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2

/-! ### The main-term coefficient and the singular-series target -/

/-- The Maynard main-term coefficient: the exact coefficient of the
    li-differences in `bvMainTerm` for the model M = li/φ, summed over
    good support pairs (bad pairs contribute 0, as in `bvMainTerm`).
    The singular-series evaluation is the computation of this sum. -/
noncomputable def maynardMainCoeff {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (m : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    maynardLambda m R d * maynardLambda m R e *
      (∑ i, if goodPair h d e i then
        ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
        else 0)

/-- The coefficient is exactly what multiplies the li-differences in
    the BV main term: `bvMainTerm` for M = li/φ unfolds into
    λ_d λ_e times (li(y + hᵢ) - li(x + hᵢ)) times the coefficient's
    summand. So evaluating `maynardMainCoeff` IS the singular-series
    step; nothing else stands between it and the main term. -/
theorem bvMainTerm_maynard_eq {k : ℕ} (h : Fin k → ℕ) (R m : ℕ)
    (li : ℝ → ℝ) (x y : ℕ) :
    bvMainTerm k h R (maynardLambda m R) (fun Y L => li Y / (Nat.totient L : ℝ)) x y
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          maynardLambda m R d * maynardLambda m R e *
            (∑ i, if goodPair h d e i then
              (li (y + h i) - li (x + h i)) *
                ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0) := by
  classical
  unfold bvMainTerm bvMainSummand
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hg : goodPair h d e i
  · simp only [if_pos hg]
    rw [div_sub_div_same, div_eq_mul_inv, Nat.cast_add, Nat.cast_add]
  · simp only [if_neg hg]

/-- Crude bound on the coefficient: |coeff| ≤ Λ · k (each good-pair
    reciprocal totient is at most 1, and there are k coordinates).
    The singular-series evaluation would replace this by
    𝔖(h) × (cutoff integral) — that replacement is the open step. -/
theorem abs_maynardMainCoeff_le {k : ℕ} (h : Fin k → ℕ) (R m : ℕ) :
    abs (maynardMainCoeff h R m)
      ≤ (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (maynardLambda m R d * maynardLambda m R e)) * k := by
  classical
  have hinner : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (∑ i, if goodPair h d e i then
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
          else 0) ≤ k := by
    intro d _ e _
    calc abs (∑ i, if goodPair h d e i then
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
            else 0)
        ≤ ∑ i, abs (if goodPair h d e i then
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
            else 0) :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hg : goodPair h d e i
          · rw [if_pos hg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
            by_cases hL : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = 0
            · rw [hL]
              simp
            · have hφ : (1 : ℝ) ≤
                  Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by
                have hpos : 0 <
                    Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
                  Nat.totient_pos.mpr (Nat.pos_of_ne_zero hL)
                exact_mod_cast hpos
              exact inv_le_one_of_one_le₀ hφ
          · rw [if_neg hg]
            simp
      _ = k := by simp
  unfold maynardMainCoeff
  calc abs (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          maynardLambda m R d * maynardLambda m R e *
            (∑ i, if goodPair h d e i then
              ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0))
      ≤ ∑ d ∈ tupleSupport k R, abs (∑ e ∈ tupleSupport k R,
          maynardLambda m R d * maynardLambda m R e *
            (∑ i, if goodPair h d e i then
              ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0)) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (maynardLambda m R d * maynardLambda m R e *
            (∑ i, if goodPair h d e i then
              ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0)) :=
        Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (maynardLambda m R d * maynardLambda m R e) * k := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hinner d hd e he) (abs_nonneg _)
    _ = (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
          abs (maynardLambda m R d * maynardLambda m R e)) * k := by
        simp only [← Finset.sum_mul]

/-- The truncated singular series for the tuple h: ∏_{p ≤ z}
    (1 - ω_p(h)/p) · (1 - 1/p)^{-k}, where ω_p(h) is the number of
    distinct residues of h mod p. The full singular series 𝔖(h) is
    the limit z → ∞; its convergence and the identification of
    `maynardMainCoeff` with 𝔖(h) × (cutoff integral) are open. -/
noncomputable def maynardSingularSeriesTrunc {k : ℕ} (h : Fin k → ℕ)
    (z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (z + 1)).filter (fun p => Nat.Prime p),
    (1 - ((Finset.univ.image (fun i => h i % p)).card : ℝ) / (p : ℝ)) *
      ((1 - (1 : ℝ) / (p : ℝ))⁻¹) ^ k

/-- The truncated product is nonnegative (each local factor is: at
    most p distinct residues mod p, and 1 - 1/p > 0 for prime p). -/
theorem maynardSingularSeriesTrunc_nonneg {k : ℕ} (h : Fin k → ℕ)
    (z : ℕ) : 0 ≤ maynardSingularSeriesTrunc h z := by
  unfold maynardSingularSeriesTrunc
  apply Finset.prod_nonneg
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpz, hpprime⟩ := hp
  have hp2 : 2 ≤ p := hpprime.two_le
  have hp0 : 0 < p := by omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hω : ((Finset.univ.image (fun i => h i % p)).card : ℝ) ≤ p := by
    have hcard : (Finset.univ.image (fun i => h i % p)).card ≤ p := by
      calc (Finset.univ.image (fun i => h i % p)).card
          ≤ (Finset.range p).card := Finset.card_le_card (by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨i, _, hi⟩ := hx
            rw [Finset.mem_range, ← hi]
            exact Nat.mod_lt _ hp0)
        _ = p := Finset.card_range p
    exact_mod_cast hcard
  have h1 : 0 ≤ 1 - ((Finset.univ.image (fun i => h i % p)).card : ℝ) / (p : ℝ) := by
    rw [sub_nonneg]
    exact (div_le_one hppos).mpr hω
  have h2 : 0 ≤ ((1 - (1 : ℝ) / (p : ℝ))⁻¹) ^ k := by
    apply pow_nonneg
    apply inv_nonneg.mpr
    rw [sub_nonneg, div_le_one hppos]
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1
  exact mul_nonneg h1 h2

/-- The cutoff integral over the simplex: ∫_{tᵢ ≥ 0, ∑ tᵢ ≤ 1} F_m(t)².
    The singular-series evaluation would identify `maynardMainCoeff`
    with 𝔖(h) times this integral (up to the (log R) normalization,
    whose exact power is part of the open computation). Stated here
    only to make the target precise; no property of it is claimed. -/
noncomputable def maynardCutoffIntegral (m k : ℕ) : ℝ :=
  ∫ t : Fin k → ℝ in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1},
    (maynardCutoff m t) ^ 2

/-- The Maynard weight plugs into the existing GPY weight and is
    nonnegative, as every squared weight is. -/
theorem maynardWeight_nonneg (k : ℕ) (h : Fin k → ℕ) (R m : ℕ) (n : ℕ) :
    0 ≤ weight k h R (maynardLambda m R) n :=
  weight_nonneg k h R (maynardLambda m R) n



/-- Λ-mass bound for the Maynard weights, restated with all local
    definitions occurring in the statement unfolded. Identical content
    to `maynardLambdaMass_le`; only the statement form differs. -/
theorem maynardLambdaMass_le_restated (m R : ℕ) {k : ℕ} :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))))
      ≤ ((R : ℝ) ^ k) ^ 2 := by
  have hmain := maynardLambdaMass_le m R (k := k)
  unfold tupleSupport maynardLambda maynardCutoff at hmain
  exact hmain

/-- Exact coefficient identification of the BV main term for the
    Maynard weights, restated with all local definitions occurring in
    the statement unfolded. Identical content to
    `bvMainTerm_maynard_eq`; only the statement form differs.
    Cast-placement note: on the left, the model lambda is applied to
    ℕ arguments, so after beta-reduction li takes ↑(y + h i); on the
    right, the original statement writes `li (y + h i)` with li :
    ℝ → ℝ, so elaboration casts the summands individually
    (li (↑y + ↑(h i))). The two sides therefore use different cast
    placements, exactly as in the original, and the restated statement
    preserves both. -/
theorem bvMainTerm_maynard_eq_restated {k : ℕ} (h : Fin k → ℕ) (R m : ℕ)
    (li : ℝ → ℝ) (x y : ℕ) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))
          * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              then li ((y + h i : ℕ) : ℝ)
                / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
                - li ((x + h i : ℕ) : ℝ)
                / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
              else 0))
      = ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))
          * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              then (li (y + h i) - li (x + h i))
                * ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0) := by
  have hmain := bvMainTerm_maynard_eq h R m li x y
  unfold bvMainTerm bvMainSummand goodPair tupleSupport maynardLambda
    maynardCutoff at hmain
  exact hmain



end GPY

theorem solution (m R : ℕ) {k : ℕ} :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))))
      ≤ ((R : ℝ) ^ k) ^ 2 := GPY.maynardLambdaMass_le_restated m R
