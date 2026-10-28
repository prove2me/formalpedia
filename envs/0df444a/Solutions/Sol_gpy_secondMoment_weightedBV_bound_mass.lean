-- Prove2me | solution 1 for gpy_secondMoment_weightedBV_bound_mass
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T17:41:12.243009+00:00
-- url     : https://prove2.me/submissions/8321cbae-bec8-4560-868e-b415f1e91745

/-
  Submission file for the Prove2Me problem `gpy_secondMoment_weightedBV_bound_mass`
  (GPY second moment: weighted BV error bound with lambda-mass fiber bound).

  Self-contained: imports Mathlib only. Contains the verified bodies of
  GPYWeights.lean, GPYCount.lean, GPYMainTerm.lean, GPYSecondMoment.lean,
  GPYBV.lean, GPYBVErr.lean, GPYBVInst.lean, GPYWeightedBV.lean, and
  GPYWeightedBVRestated.lean, with top-level `theorem solution` in the
  problem's exact binder/statement form (statement mechanically extracted
  from the restated theorem, so the two are textually identical).
  No sorry tactic, no axioms beyond the standard ones, no platform imports.
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



/-- Tight single-residue error bound, restated with all local definitions
    occurring in the statement unfolded. Identical content to
    `secondMoment_tightErrBound`; only the statement form differs. -/
theorem secondMoment_tightErrBound_restated (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e) * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ wit d e i + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              + abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ wit d e i + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            else 1) := by
  have hmain := secondMoment_tightErrBound k h R lam M hxy wit hwit
  unfold secondMoment primeInd weight tupleSupport bvMainTerm bvMainSummand
    goodPair tightErrBound tightErrSummand primeCountAP at hmain
  exact hmain

/-- Grouped error bound, restated with all local definitions occurring in
    the statement unfolded. Identical content to
    `secondMoment_groupedErrBound`; only the statement form differs. -/
theorem secondMoment_groupedErrBound_restated (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          (∑ p ∈ ((Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R) ×ˢ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R)).filter
              (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
            abs (lam p.1 * lam p.2)) * ((if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (y + h i) L))).Nonempty then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (y + h i) L))).max' hne else 0) + (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (x + h i) L))).Nonempty then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (x + h i) L))).max' hne else 0)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := by
  have hmain := secondMoment_groupedErrBound k h R lam M hxy wit hwit
  unfold secondMoment primeInd weight tupleSupport bvMainTerm bvMainSummand
    goodPair fiberWeight maxCoprimeErr primeCountAP at hmain
  exact hmain

/-- Weighted BV error bound, restated with all local definitions occurring
    in the statement unfolded. Identical content to
    `secondMoment_weightedBV_bound`; only the statement form differs. -/
theorem secondMoment_weightedBV_bound_restated (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i)
    (Wbar : ℝ) (hWnn : 0 ≤ Wbar)
    (hW : ∀ i L, (∑ p ∈ ((Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R) ×ˢ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R)).filter
              (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
            abs (lam p.1 * lam p.2)) ≤ Wbar) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ Wbar * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := by
  have hmain := secondMoment_weightedBV_bound k h R lam M hxy wit hwit B hBV hlevel hY2
    Wbar hWnn hW
  unfold secondMoment primeInd weight tupleSupport bvMainTerm bvMainSummand
    goodPair at hmain
  exact hmain

/-- Weighted BV error bound with lambda-mass fiber bound, restated with all
    local definitions occurring in the statement unfolded. Identical content
    to `secondMoment_weightedBV_bound_mass`; only the statement form differs. -/
theorem secondMoment_weightedBV_bound_mass_restated (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e))
          * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := by
  have hmain := secondMoment_weightedBV_bound_mass k h R lam M hxy wit hwit B hBV hlevel hY2
  unfold secondMoment primeInd weight tupleSupport bvMainTerm bvMainSummand
    goodPair at hmain
  exact hmain



end GPY

theorem solution (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e))
          * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := GPY.secondMoment_weightedBV_bound_mass_restated k h R lam M hxy wit hwit B hBV hlevel hY2
