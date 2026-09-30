-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:15:20.402373+00:00
-- url     : https://prove2.me/submissions/ab93ee58-8db6-49bf-b41b-4c13e5d9f6da

import Mathlib
import Definitions.Def_matrix_completion_neumann
import Definitions.Def_linear_neumann_offdiag_bernstein

set_option autoImplicit false
namespace StructuralMiddleProof




set_option autoImplicit false

namespace UniformInnerProof

set_option autoImplicit false

namespace NeumannProof

-- Accepted proof by Aphrodite; submission c878d05d-e191-47c8-a2bb-113f888b7985.
-- Original source SHA-256: 807732c32c851f542349b627f3ade5c5fe48726d82384913e3e5f8ce5023430f.
namespace NeumannDependency0
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_prod_factor`.

**Independence / product factorization of the Bernoulli powerset expectation.**
For any per-coordinate function `f : (Fin n₁ × Fin n₂) → ℝ → ℝ`, the expectation
of the product `∏_w f w (𝟙[w ∈ Ω])` over the Bernoulli powerset measure with
inclusion probability `p` factorizes into a product of per-coordinate
expectations `p·f w 1 + (1-p)·f w 0`. This is the precise statement that the
coordinate inclusion indicators `𝟙[w ∈ Ω]` are independent under the powerset
measure, proved directly by the binomial expansion `Finset.prod_add`
(`∏_w (a_w + b_w) = ∑_{Ω⊆univ} (∏_{w∈Ω} a_w)(∏_{w∉Ω} b_w)`). -/
theorem bernoulli_powerset_expectation_prod_factor {n₁ n₂ : ℕ} (p : ℝ)
    (f : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      ∏ w : Fin n₁ × Fin n₂, (p * f w 1 + (1 - p) * f w 0) := by
  classical
  have hpa := Finset.prod_add (fun w : Fin n₁ × Fin n₂ => p * f w 1)
    (fun w => (1 - p) * f w 0) Finset.univ
  rw [hpa, Finset.powerset_univ]
  unfold bernoulliExpectation bernoulliObservationWeight
  apply Finset.sum_congr rfl
  intro t _
  simp only []
  have hsplit :
      (∏ w : Fin n₁ × Fin n₂, f w (if w ∈ t then 1 else 0)) =
        (∏ w ∈ t, f w 1) * ∏ w ∈ Finset.univ \ t, f w 0 := by
    rw [← Finset.prod_mul_prod_compl t (fun w => f w (if w ∈ t then 1 else 0)),
        Finset.compl_eq_univ_sdiff]
    congr 1
    · apply Finset.prod_congr rfl; intro w hw; simp [hw]
    · apply Finset.prod_congr rfl; intro w hw
      simp only [Finset.mem_sdiff] at hw; simp [hw.2]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, hsplit]
  rw [Finset.card_univ_diff]; ring
end NeumannDependency0
export NeumannDependency0 (bernoulli_powerset_expectation_prod_factor)

-- Accepted proof by Aphrodite; submission 50cd47e2-8a2e-4eb1-9724-8f9afa5dfe28.
-- Original source SHA-256: eed308f01ca5e9b1db71c6c7b2f33f22a6fc1d587d7084b40683592e968e2374.
namespace NeumannDependency1
open MatrixCompletion
open scoped BigOperators Classical

/-- Reduction of the MGF factorization onto the Proved independence/product
factorization `bernoulli_powerset_expectation_prod_factor`. -/
theorem centered_sampling_coefficient_mgf_factorization {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) =
      ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) := by
  classical
  set f : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun w x => Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (x - p))) with hf
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p f
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      (fun Omega =>
        Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) := by
    funext Omega
    have hcoeff : matrixEntrySum (centeredSamplingFluctuation Omega p B) =
        ∑ w : Fin n₁ × Fin n₂,
          (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)) := by
      unfold matrixEntrySum centeredSamplingFluctuation
      apply Finset.sum_congr rfl
      intro w _
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      unfold samplingProjection
      by_cases h : (w.1, w.2) ∈ Omega
      · simp only [h, if_true]; ring
      · simp only [h, if_false]; ring
    rw [hcoeff, Finset.mul_sum, Real.exp_sum]
  rw [hL] at key
  rw [key]
end NeumannDependency1
export NeumannDependency1 (centered_sampling_coefficient_mgf_factorization)

-- Accepted proof by Aphrodite; submission 0ff2689a-aa4a-42ae-8398-bffa9555324d.
-- Original source SHA-256: 404efc41ced0363638d3bab01aafc0f14fa0d6d55d7d5a65459964e616f612aa.
namespace NeumannDependency2
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem exp_le_quad (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x^2 := by
  set phi : ℝ → ℝ := fun t => Real.exp (-t) * (1 + t + t^2) with hphi
  have hderiv : ∀ t : ℝ, HasDerivAt phi (Real.exp (-t) * (t * (1 - t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t :=
      (hasDerivAt_neg t).exp.congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => 1 + t + t^2) (1 + 2*t) t :=
      (((hasDerivAt_id t).const_add 1).add (hasDerivAt_pow 2 t)).congr_deriv (by norm_num)
    rw [hphi]
    exact (h1.mul h2).congr_deriv (by ring)
  have hphi0 : phi 0 = 1 := by simp [hphi]
  have hge : 1 ≤ phi x := by
    rcases lt_or_ge x 0 with hx0 | hx0
    · -- x < 0 : phi antitone on Iic 0, so phi x ≥ phi 0
      have hanti : AntitoneOn phi (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Iic] at ht
          have ht0 : t < 0 := ht
          have hneg : t * (1 - t) ≤ 0 := by nlinarith [ht0]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          nlinarith [mul_nonneg hexp.le (neg_nonneg.mpr hneg)]
      have := hanti (Set.mem_Iic.mpr (le_of_lt hx0)) (Set.mem_Iic.mpr le_rfl) (le_of_lt hx0)
      rwa [hphi0] at this
    · -- 0 ≤ x : phi monotone on Icc 0 1, so phi x ≥ phi 0
      have hmono : MonotoneOn phi (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Icc] at ht
          have ht0 : 0 < t := ht.1
          have ht1 : t < 1 := ht.2
          have hge0 : 0 ≤ t * (1 - t) := by nlinarith [ht0, ht1]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          positivity
      have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩) (Set.mem_Icc.mpr ⟨hx0, hx⟩) hx0
      rwa [hphi0] at this
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hge' : 1 ≤ Real.exp (-x) * (1 + x + x^2) := hge
  rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ hexp] at hge'
  linarith [hge']
end NeumannDependency2
export NeumannDependency2 (exp_le_quad)

-- Accepted proof by Aphrodite; submission a96f36f9-5621-4e58-9efd-849fc99fb54e.
-- Original source SHA-256: e566acfae54e24a4c7663f15865555055e2f1415700a081777b9ac23bb3ad8bb.
namespace NeumannDependency3
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem two_point_bernstein_mgf (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcent : p * a + (1 - p) * b = 0) (ha : a ≤ 1) (hb : b ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a^2 + (1 - p) * b^2) := by
  have hEa := exp_le_quad a ha
  have hEb := exp_le_quad b hb
  have h1p : (0:ℝ) ≤ 1 - p := by linarith
  have hV : (0:ℝ) ≤ p * a^2 + (1 - p) * b^2 := by positivity
  -- p e^a + (1-p) e^b ≤ 1 + (pa+(1-p)b) + V = 1 + 0 + V = 1 + V
  have hcomb : p * Real.exp a + (1 - p) * Real.exp b ≤ 1 + (p*a^2 + (1-p)*b^2) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hEa hp0)
                         (mul_le_mul_of_nonneg_left hEb h1p)
    nlinarith [h, hcent]
  -- 1 + V ≤ exp V
  have hexpV : 1 + (p*a^2 + (1-p)*b^2) ≤ Real.exp (p*a^2 + (1-p)*b^2) := by
    have := Real.add_one_le_exp (p*a^2 + (1-p)*b^2); linarith
  linarith [hcomb, hexpV]
end NeumannDependency3
export NeumannDependency3 (two_point_bernstein_mgf)

-- Accepted proof by Aphrodite; submission 03179121-d9f3-4e8d-b5ad-44627a812696.
-- Original source SHA-256: 359ea8d26c6c0cd9c8ed0168cabdc670499635c486b3cf38bd2737add8a60c11.
namespace NeumannDependency4
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Bernstein (variance-scaled) MGF bound** for the centered-sampling coefficient.
For `0 < p ≤ 1`, `‖B‖_∞ ≤ entryScale`, `0 < entryScale`, and
`0 ≤ lam ≤ p / entryScale` (so each per-coordinate increment stays in range),
`E[exp(lam·Coeff)] ≤ exp(lam²·(1-p)/p·‖B‖_F²)`. The exponent carries the TRUE
variance `(1-p)/p·‖B‖_F²` (∼1/p), unlike the Hoeffding/sub-Gaussian range proxy
(∼1/p²). -/
theorem centered_sampling_coefficient_bernstein_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (entryScale lam : ℝ)
    (hent : entrySupNorm B ≤ entryScale) (hes : 0 < entryScale)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ p / entryScale) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
  classical
  have hpne : p ≠ 0 := ne_of_gt hp0
  -- Per-entry bound |B_w| ≤ entryScale.
  have hBw : ∀ w : Fin n₁ × Fin n₂, |B w.1 w.2| ≤ entryScale := by
    intro w
    refine le_trans ?_ hent
    have hbdd2 : ∀ i : Fin n₁, BddAbove (Set.range (fun j : Fin n₂ => |B i j|)) :=
      fun i => Set.Finite.bddAbove (Set.finite_range _)
    have hbdd1 : BddAbove (Set.range (fun i : Fin n₁ => ⨆ j : Fin n₂, |B i j|)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    unfold entrySupNorm
    refine le_trans (le_ciSup (hbdd2 w.1) w.2) ?_
    exact le_ciSup hbdd1 w.1
  -- Key per-coordinate range bound: lam * |B_w| / p ≤ 1.
  have hkey : ∀ w : Fin n₁ × Fin n₂, lam * |B w.1 w.2| / p ≤ 1 := by
    intro w
    rw [div_le_one hp0]
    -- lam * |B_w| ≤ lam * entryScale ≤ p   (lam*entryScale ≤ p from lam ≤ p/entryScale)
    have h1 : lam * |B w.1 w.2| ≤ lam * entryScale :=
      mul_le_mul_of_nonneg_left (hBw w) hlam0
    have h2 : lam * entryScale ≤ p := by
      rw [le_div_iff₀ hes] at hlam; linarith [hlam]
    linarith
  rw [centered_sampling_coefficient_mgf_factorization p B lam]
  -- bound each factor by the per-coord variance exponential.
  have hfac : ∀ w : Fin n₁ × Fin n₂,
      (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
    intro w
    -- Define the two values a (prob p) and b (prob 1-p) of the centered increment.
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    have hkw := hkey w
    -- centering
    have hcent : p * (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))) = 0 := by
      field_simp; ring
    -- a ≤ 1
    have ha1 : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| * (1 - p) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) h1p
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (1 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (1 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]
    -- b ≤ 1
    have hb1 : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (0 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (0 - p) = -(B w.1 w.2) * p := by ring
          _ ≤ |B w.1 w.2| * p := mul_le_mul_of_nonneg_right (neg_le_abs _) (le_of_lt hp0)
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (0 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (0 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]
    have hH := two_point_bernstein_mgf p
      (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
      (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))
      (le_of_lt hp0) hp1 hcent ha1 hb1
    refine hH.trans ?_
    apply Real.exp_le_exp.mpr
    apply le_of_eq
    field_simp; ring
  calc ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))))
      ≤ ∏ w : Fin n₁ × Fin n₂, Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        apply Finset.prod_le_prod
        · intro w _
          have h1p : (0:ℝ) ≤ 1 - p := by linarith
          have e1 := mul_nonneg (le_of_lt hp0) (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))).le
          have e2 := mul_nonneg h1p (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))).le
          linarith
        · intro w _; exact hfac w
    _ = Real.exp (∑ w : Fin n₁ × Fin n₂, lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        rw [← Real.exp_sum]
    _ = Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
        congr 1
        rw [frobeniusNormSq, ← Fintype.sum_prod_type']
        rw [Finset.mul_sum]
end NeumannDependency4
export NeumannDependency4 (centered_sampling_coefficient_bernstein_mgf)

-- Accepted proof by Aphrodite; submission babaa216-33ba-4373-96d9-45e3064a4981.
-- Original source SHA-256: 486d0a8537415d344ec7f02f1ef24202651c4e8c60a8bfec693ab2b9a33c9299.
namespace NeumannDependency5
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem rpow_mul_exp_neg_le (q lam x : ℝ) (hq : 0 < q) (hlam : 0 < lam) (hx : 0 ≤ x) :
    x ^ q * Real.exp (-(lam * x)) ≤ (q / (lam * Real.exp 1)) ^ q := by
  -- Work in logs (both sides positive when x>0; x=0 handled separately).
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- x = 0 : LHS = 0^q * 1 = 0 ≤ RHS (RHS > 0).
    rw [← hx0]
    rw [Real.zero_rpow (ne_of_gt hq)]
    simp only [zero_mul]
    positivity
  · -- x > 0
    have hRpos : 0 < q / (lam * Real.exp 1) := by positivity
    have hLpos : 0 < x ^ q * Real.exp (-(lam * x)) := by
      have := Real.rpow_pos_of_pos hxpos q
      positivity
    rw [← Real.log_le_log_iff hLpos (Real.rpow_pos_of_pos hRpos q)]
    -- log LHS = q log x - lam x ;  log RHS = q (log q - log lam - 1)
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hxpos q)) (ne_of_gt (Real.exp_pos _))]
    rw [Real.log_rpow hxpos, Real.log_exp, Real.log_rpow hRpos]
    -- goal: q*log x + (-(lam x)) ≤ q * log(q/(lam e))
    -- log(q/(lam e)) = log q - log(lam) - 1
    have hlogR : Real.log (q / (lam * Real.exp 1)) = Real.log q - Real.log lam - 1 := by
      rw [Real.log_div (ne_of_gt hq) (by positivity),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
      ring
    rw [hlogR]
    -- Need: q log x - lam x ≤ q(log q - log lam - 1)
    -- ⟺ lam x ≥ q log x - q log q + q log lam + q = q(log(lam x/q)) + q  ⟺ lam x/q ≥ log(lam x/q)+1
    -- u := lam x / q > 0; use log u ≤ u - 1.
    set u := lam * x / q with hu
    have hupos : 0 < u := by rw [hu]; positivity
    have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    -- log u = log lam + log x - log q
    have hlu : Real.log u = Real.log lam + Real.log x - Real.log q := by
      rw [hu, Real.log_div (by positivity) (ne_of_gt hq),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt hxpos)]
    rw [hlu] at hlogu
    -- hlogu : log lam + log x - log q ≤ lam x/q - 1.  Multiply by q>0.
    have := mul_le_mul_of_nonneg_left hlogu (le_of_lt hq)
    -- q(log lam + log x - log q) ≤ q(lam x/q - 1) = lam x - q
    have hrhs : q * (lam * x / q - 1) = lam * x - q := by field_simp
    rw [hrhs] at this
    nlinarith [this]
end NeumannDependency5
export NeumannDependency5 (rpow_mul_exp_neg_le)

-- Accepted proof by Aphrodite; submission 1f271913-3fe3-474b-9c0f-917cda8b82d1.
-- Original source SHA-256: 8d533ed97bc218a293100783d6dd26228b4df93577f061b1f24a4e05fe65ba3d.
namespace NeumannDependency6
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Moment-from-MGF on the Bernoulli powerset measure.** If a real statistic `Z`
has both-sided MGF bounded by `M` at parameter `lam > 0`
(`E[e^{lam·Z}] ≤ M` and `E[e^{-lam·Z}] ≤ M`), then for every real `q > 0`,
`E[|Z|^q] ≤ 2·(q/(lam·e))^q·M`. (Cramér–Chernoff moment device.) -/
theorem bernoulli_moment_from_two_sided_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (lam M q : ℝ)
    (hlam : 0 < lam) (hq : 0 < q)
    (hMGFpos : bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) ≤ M)
    (hMGFneg : bernoulliExpectation p (fun Omega => Real.exp (-(lam * Z Omega))) ≤ M) :
    bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤
      2 * (q / (lam * Real.exp 1)) ^ q * M := by
  classical
  -- pointwise: |Z Ω|^q ≤ (q/(lam e))^q (e^{lam Z}+e^{-lam Z}).
  have hpoint : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      |Z Omega| ^ q ≤ (q / (lam * Real.exp 1)) ^ q *
        (Real.exp (lam * Z Omega) + Real.exp (-(lam * Z Omega))) := by
    intro Om
    -- |Z|^q * e^{-lam|Z|} ≤ (q/(lam e))^q  ⇒ |Z|^q ≤ (q/(lam e))^q e^{lam|Z|}
    have hx : (0:ℝ) ≤ |Z Om| := abs_nonneg _
    have hbase := rpow_mul_exp_neg_le q lam (|Z Om|) hq hlam hx
    have hepos : (0:ℝ) < Real.exp (-(lam * |Z Om|)) := Real.exp_pos _
    -- |Z|^q ≤ (q/(lam e))^q * e^{lam|Z|}
    have hstep : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
      have hle : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) :=
        (le_div_iff₀ hepos).mpr hbase
      calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) := hle
        _ = (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
            rw [Real.exp_neg, div_inv_eq_mul]
    -- e^{lam|Z|} ≤ e^{lam Z}+e^{-lam Z}
    have hexpabs : Real.exp (lam * |Z Om|) ≤ Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)) := by
      rcases abs_cases (Z Om) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he]
        have : (0:ℝ) ≤ Real.exp (-(lam * Z Om)) := (Real.exp_pos _).le
        linarith
      · rw [he]
        have hpos : (0:ℝ) ≤ Real.exp (lam * Z Om) := (Real.exp_pos _).le
        have : lam * -(Z Om) = -(lam * Z Om) := by ring
        rw [this]; linarith
    calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := hstep
      _ ≤ (q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om))) := by
          apply mul_le_mul_of_nonneg_left hexpabs (by positivity)
  -- Take bernoulliExpectation: linear with nonneg weights.
  unfold bernoulliExpectation
  have hwnn : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om; unfold bernoulliObservationWeight
    have : (0:ℝ) ≤ 1 - p := by linarith
    positivity
  -- ∑ w |Z|^q ≤ ∑ w (q/(lam e))^q (e^{lamZ}+e^{-lamZ}) = (q/(lam e))^q (∑w e^{lamZ}+∑w e^{-lamZ})
  calc ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * |Z Om| ^ q
      ≤ ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om *
          ((q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)))) := by
        apply Finset.sum_le_sum
        intro Om _
        exact mul_le_mul_of_nonneg_left (hpoint Om) (hwnn Om)
    _ = (q / (lam * Real.exp 1)) ^ q *
          ((∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (lam * Z Om))
           + (∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (-(lam * Z Om)))) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro Om _; ring
    _ ≤ (q / (lam * Real.exp 1)) ^ q * (M + M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hMGFpos hMGFneg
    _ = 2 * (q / (lam * Real.exp 1)) ^ q * M := by ring
end NeumannDependency6
export NeumannDependency6 (bernoulli_moment_from_two_sided_mgf)

-- Accepted proof by Aphrodite; submission fac29f89-d88a-4043-9f3c-bb4fee69d7b0.
-- Original source SHA-256: d7ae1a6e5e4ddb04cd2c2fc5e67ebc5448dd634dd5674f656833e30482b92a05.
namespace NeumannDependency7
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

namespace ProveAA

variable {n₁ n₂ : ℕ}

/-- -Coeff Ω = Coeff of -B. -/
theorem coeff_neg (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Om : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Om p (-B)) =
      -(matrixEntrySum (centeredSamplingFluctuation Om p B)) := by
  unfold matrixEntrySum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  show p⁻¹ * ((samplingProjection Om (-B)) w.1 w.2 - p * (-B) w.1 w.2)
      = -(p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2))
  by_cases h : (w.1, w.2) ∈ Om <;>
    simp [samplingProjection, Matrix.neg_apply, h] <;> ring

theorem entrySup_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm (-B) = entrySupNorm B := by
  unfold entrySupNorm; simp only [Matrix.neg_apply, abs_neg]

theorem frobSq_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq (-B) = frobeniusNormSq B := by
  unfold frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.neg_apply]; ring

theorem bound_step (q p V E frob : ℝ) (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hV : 0 < V) (hE : 0 < E) (hfrob : 0 ≤ frob) (hVfrob : V ≤ frob^2 / p) :
    2 * (q / (Real.exp 1 * (min (Real.sqrt (q/(2*V)) ) (p/E)))) ^ q
        * Real.exp (min (Real.sqrt (q/(2*V))) (p/E)^2 * V) ≤
      (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
  set lam := min (Real.sqrt (q/(2*V))) (p/E) with hlamdef
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hsqrtpos : 0 < Real.sqrt (q/(2*V)) := Real.sqrt_pos.mpr (by positivity)
  have hpEpos : 0 < p/E := by positivity
  have hlampos : 0 < lam := lt_min hsqrtpos hpEpos
  have hlamA : lam ≤ Real.sqrt (q/(2*V)) := min_le_left _ _
  have hlamB : lam ≤ p/E := min_le_right _ _
  have hlam2V : lam^2 * V ≤ q/2 := by
    have h1 : lam^2 ≤ q/(2*V) := by
      have hh := Real.sq_sqrt (show (0:ℝ) ≤ q/(2*V) by positivity)
      nlinarith [hlamA, hlampos, Real.sqrt_nonneg (q/(2*V)), hh,
        mul_le_mul hlamA hlamA hlampos.le (Real.sqrt_nonneg _)]
    have heq : (q/(2*V)) * V = q/2 := by
      rw [div_mul_eq_mul_div, mul_comm 2 V, ← div_div, mul_div_assoc, div_self (ne_of_gt hV), mul_one]
    have : lam^2 * V ≤ (q/(2*V)) * V := mul_le_mul_of_nonneg_right h1 hV.le
    rw [heq] at this; linarith [this]
  have hexp : Real.exp (lam^2 * V) ≤ Real.exp (q/2) := Real.exp_le_exp.mpr hlam2V
  -- q/lam ≤ √(2Vq) + (q/p)·E
  have hqlam : q / lam ≤ Real.sqrt (2*V*q) + (q/p) * E := by
    rw [div_le_iff₀ hlampos]
    rcases le_total (Real.sqrt (q/(2*V))) (p/E) with hcase | hcase
    · have hl : lam = Real.sqrt (q/(2*V)) := by rw [hlamdef, min_eq_left hcase]
      rw [hl]
      have hsq : Real.sqrt (2*V*q) * Real.sqrt (q/(2*V)) = q := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show (2*V*q) * (q/(2*V)) = q^2 by field_simp]
        rw [Real.sqrt_sq hqpos.le]
      have hrest : 0 ≤ (q/p) * E * Real.sqrt (q/(2*V)) := by positivity
      nlinarith [hsq, hrest]
    · have hl : lam = p/E := by rw [hlamdef, min_eq_right hcase]
      rw [hl]
      have hqpE : (q/p) * E * (p/E) = q := by field_simp
      have hrest : 0 ≤ Real.sqrt (2*V*q) * (p/E) := by positivity
      nlinarith [hqpE, hrest]
  have hsqrt2Vq : Real.sqrt (2*V*q) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) := by
    have hrw : Real.sqrt 2 * (Real.sqrt (q/p) * frob) = Real.sqrt (2 * (q/p) * frob^2) := by
      rw [show (2 * (q/p) * frob^2) = 2 * ((q/p) * frob^2) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [Real.sqrt_mul (div_nonneg hqpos.le hp0.le), Real.sqrt_sq hfrob]
    rw [hrw]
    apply Real.sqrt_le_sqrt
    have hVq : V * q ≤ (frob^2/p) * q := mul_le_mul_of_nonneg_right hVfrob hqpos.le
    have : (frob^2/p) * q = 2 * (q/p) * frob^2 / 2 := by ring
    nlinarith [hVq, hqpos]
  have hJ : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := by
    linarith [hqlam, hsqrt2Vq]
  -- merge exp(q/2) into the power base.
  have hmerge : (q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)
      = (q / (lam * Real.exp (1/2))) ^ q := by
    have he2 : Real.exp (q/2) = (Real.exp (1/2)) ^ q := by rw [← Real.exp_mul]; ring_nf
    rw [he2, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    have hexp1 : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
    rw [hexp1]; field_simp
  -- step: 2 A^q exp(lam²V) ≤ 2 A^q exp(q/2) = 2 (q/(lam exp½))^q
  have hstep1 : 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := by
    have h := mul_le_mul_of_nonneg_left hexp
      (show (0:ℝ) ≤ 2 * (q / (Real.exp 1 * lam)) ^ q by positivity)
    calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
        = (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (lam^2 * V) := by ring
      _ ≤ (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (q/2) := h
      _ = 2 * ((q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)) := by ring
      _ = 2 * (q / (lam * Real.exp (1/2))) ^ q := by rw [hmerge]
  -- base bound: q/(lam exp½) ≤ √2(√(q/p)frob+(q/p)E)
  have hbase : q / (lam * Real.exp (1/2)) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
    have hexphalf : (1:ℝ) ≤ Real.exp (1/2) := Real.one_le_exp (by norm_num)
    have h1 : q / (lam * Real.exp (1/2)) ≤ q / lam := by
      rw [div_le_div_iff₀ (by positivity) hlampos]
      have : lam ≤ lam * Real.exp (1/2) := by nlinarith [hlampos, hexphalf]
      nlinarith [hqpos, hlampos, this]
    have hJ' : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
      have hsqrt2 : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      have hnn : 0 ≤ (q/p) * E := by positivity
      calc q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := hJ
        _ ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + Real.sqrt 2 * ((q/p) * E) := by nlinarith [hsqrt2, hnn]
        _ = Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by ring
    linarith [h1, hJ']
  -- raise to q-th power.
  have hJnn : 0 ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by positivity
  have hpow : (q / (lam * Real.exp (1/2))) ^ q ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
    Real.rpow_le_rpow (by positivity) hbase hqpos.le
  -- 2 * (√2 J')^q ≤ (2√2 J')^q  where J'=(√(q/p)frob+(q/p)E)
  have hfinal : 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q
      ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
    rw [show (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E))
          = 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) by ring]
    rw [Real.mul_rpow (by norm_num) hJnn]
    have h2q : (2:ℝ) ≤ 2 ^ q := by
      calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ 2 ^ q := Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hq
    have hbasenn : 0 ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
      Real.rpow_nonneg hJnn q
    nlinarith [h2q, hbasenn]
  calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := hstep1
    _ ≤ 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
        apply mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := hfinal

end ProveAA

open ProveAA

set_option maxHeartbeats 1600000

theorem scalar_centered_sampling_qnorm_rosenthal_estimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∀ q : ℕ, 1 ≤ q →
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (C *
                (Real.sqrt
                    ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q := by
  refine ⟨2 * Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hent hfrob q hq1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hnn : (0:ℝ) < (n₁:ℝ) * (n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hnn]; exact_mod_cast hmle
  have hentSnn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    refine Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hentS : 0 ≤ entryScale := le_trans hentSnn hent
  have hfrobS : 0 ≤ frobScale := le_trans (by unfold frobeniusNorm; positivity) hfrob
  -- nonneg of RHS base
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq1
  -- Rewrite the moment via hCoeff.
  have hmomeq : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
      = bernoulliExpectation p (fun Omega =>
          |matrixEntrySum (centeredSamplingFluctuation Omega p B)| ^ q) := by
    unfold bernoulliExpectation
    apply Finset.sum_congr rfl; intro Om _; simp only []; rw [hCoeff Om]
  rw [hmomeq]
  -- Abbreviate Z.
  set Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Om => matrixEntrySum (centeredSamplingFluctuation Om p B) with hZ
  -- RHS is nonneg.
  have hRHSnn : (0:ℝ) ≤ 2 * Real.sqrt 2 *
      (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale) := by positivity
  -- Case split: degenerate (moment = 0) vs main.
  by_cases hdeg : p = 0 ∨ p = 1 ∨ frobeniusNormSq B = 0 ∨ entryScale = 0
  · -- moment = 0 ≤ RHS
    have hmom0 : bernoulliExpectation p (fun Om => |Z Om| ^ q) = 0 := by
      rcases hdeg with h | h | h | h
      · -- p = 0
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hz : Z Om = 0 := by
          rw [hZ, h]; unfold matrixEntrySum centeredSamplingFluctuation; simp [inv_zero]
        simp only [hz, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      · -- p = 1 : weight 0 except univ; Z univ = 0
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        by_cases huniv : Om = Finset.univ
        · have hZ0 : Z Om = 0 := by
            rw [hZ, h, huniv]
            unfold matrixEntrySum
            refine Finset.sum_eq_zero (fun w _ => ?_)
            show (1:ℝ)⁻¹ *
                ((samplingProjection Finset.univ B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
            simp [samplingProjection]
          simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
        · have hw : bernoulliObservationWeight p Om = 0 := by
            rw [h]; unfold bernoulliObservationWeight
            have hcard : Om.card < Fintype.card (Fin n₁ × Fin n₂) := by
              rcases lt_or_eq_of_le (Finset.card_le_univ Om) with hlt | heq
              · simpa using hlt
              · exact absurd (Finset.card_eq_iff_eq_univ Om |>.mp (by simpa using heq)) huniv
            have hne : Fintype.card (Fin n₁ × Fin n₂) - Om.card ≠ 0 := by omega
            rw [one_pow, one_mul, show (1:ℝ)-1 = 0 by norm_num, zero_pow hne]
          rw [hw, zero_mul]
      · -- frobeniusNormSq B = 0 ⇒ B = 0 ⇒ Z = 0
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hsum : ∀ a, ∀ b, B a b ^ 2 = 0 := by
            intro a b
            have hnn2 : ∀ a, ∀ b, (0:ℝ) ≤ B a b ^ 2 := fun a b => sq_nonneg _
            unfold frobeniusNormSq at h
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (B i j)))).mp h
            have h2 := this a (Finset.mem_univ a)
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (B a j))).mp h2 b (Finset.mem_univ b)
          have := hsum i j; nlinarith [this]
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      · -- entryScale = 0 ⇒ entrySupNorm B = 0 ⇒ B = 0 ⇒ Z = 0
        have hsup0 : entrySupNorm B ≤ 0 := h ▸ hent
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hbdd2 : ∀ a : Fin n₁, BddAbove (Set.range (fun b : Fin n₂ => |B a b|)) :=
            fun a => Set.Finite.bddAbove (Set.finite_range _)
          have hbdd1 : BddAbove (Set.range (fun a : Fin n₁ => ⨆ b : Fin n₂, |B a b|)) :=
            Set.Finite.bddAbove (Set.finite_range _)
          have hle : |B i j| ≤ entrySupNorm B := by
            unfold entrySupNorm
            exact le_trans (le_ciSup (hbdd2 i) j) (le_ciSup hbdd1 i)
          have : |B i j| ≤ 0 := le_trans hle hsup0
          have := abs_nonpos_iff.mp this; exact this
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
    rw [hmom0]; positivity
  · -- MAIN: p∈(0,1), frobeniusNormSq B>0, entryScale>0.
    push_neg at hdeg
    obtain ⟨hpne0, hpne1, hFne, hEne⟩ := hdeg
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpne0)
    have hEpos : 0 < entryScale := lt_of_le_of_ne hentS (Ne.symm hEne)
    have hFpos : 0 < frobeniusNormSq B := lt_of_le_of_ne (by unfold frobeniusNormSq; positivity) (Ne.symm hFne)
    set V : ℝ := (1 - p) / p * frobeniusNormSq B with hVdef
    have hppos1 : p < 1 := lt_of_le_of_ne hp1 hpne1
    have h1mp0 : 0 < 1 - p := by linarith
    have hVpos : 0 < V := by rw [hVdef]; positivity
    -- frobScale > 0 (else frobeniusNormSq B ≤ frobScale^2 = 0)
    have hFle : frobeniusNormSq B ≤ frobScale ^ 2 := by
      have hsqle : Real.sqrt (frobeniusNormSq B) ≤ frobScale := by
        have := hfrob; unfold frobeniusNorm at this; exact this
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ frobeniusNormSq B by unfold frobeniusNormSq; positivity),
        hsqle, hfrobS, Real.sqrt_nonneg (frobeniusNormSq B)]
    have hfrobSpos : 0 < frobScale := by
      rcases lt_or_eq_of_le hfrobS with hlt | heq
      · exact hlt
      · exfalso; rw [← heq] at hFle; simp at hFle; linarith [hFpos, hFle]
    -- V ≤ frobScale^2 / p
    have hVfrob : V ≤ frobScale ^ 2 / p := by
      rw [hVdef]
      have h1mp : (1 - p) ≤ 1 := by linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hppos hppos]
      have h1 : (1-p)*frobeniusNormSq B ≤ frobeniusNormSq B := by nlinarith [h1mp, h1mp0, hFpos.le]
      have h2 : (1-p)*frobeniusNormSq B ≤ frobScale^2 := le_trans h1 hFle
      nlinarith [h2, hppos.le]
    -- choose lam = min(√(q/(2V)), p/entryScale).
    set lam : ℝ := min (Real.sqrt ((q:ℝ)/(2*V))) (p/entryScale) with hlam
    have hsqrtpos : 0 < Real.sqrt ((q:ℝ)/(2*V)) := Real.sqrt_pos.mpr (by positivity)
    have hlampos : 0 < lam := lt_min hsqrtpos (by positivity)
    have hlamE : lam ≤ p / entryScale := min_le_right _ _
    -- two-sided Bernstein MGF.
    have hMGFpos : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
        ≤ Real.exp (V * lam^2) := by
      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 B entryScale lam hent hEpos hlampos.le hlamE
      have hLHS : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p B))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _; rw [hZ]
      rw [hLHS]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring
    have hMGFneg : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
        ≤ Real.exp (V * lam^2) := by
      -- -Z = Coeff of -B; apply Bernstein to -B.
      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 (-B) entryScale lam
        (by rw [entrySup_neg]; exact hent) hEpos hlampos.le hlamE
      rw [frobSq_neg] at h
      -- h : E[exp(lam * matrixEntrySum(cSF Om p (-B)))] ≤ exp(lam^2 ((1-p)/p) frobNormSq B)
      have hrw : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p (-B)))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
        simp only [hZ, coeff_neg]; congr 1; ring
      rw [hrw]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring
    -- moment-from-MGF with M = exp(V lam^2), q := (q:ℝ).
    have hmom := bernoulli_moment_from_two_sided_mgf p hp0 hp1 Z lam (Real.exp (V * lam^2)) (q:ℝ)
      hlampos hqR hMGFpos hMGFneg
    -- hmom : E[|Z|^(q:ℝ)] ≤ 2 (q/(lam e))^q exp(V lam^2)
    -- bridge |Z|^(q:ℕ) = |Z|^((q:ℝ)).
    have hbridge : bernoulliExpectation p (fun Om => |Z Om| ^ q)
        = bernoulliExpectation p (fun Om => |Z Om| ^ (q:ℝ)) := by
      unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
      simp only []; rw [Real.rpow_natCast]
    rw [hbridge]
    refine hmom.trans ?_
    -- 2 (q/(lam e))^q exp(V lam^2) = 2 (q/(e lam))^q exp(lam^2 V) ≤ bound_step ≤ RHS
    have hbs := bound_step (q:ℝ) p V entryScale frobScale (by exact_mod_cast hq1) hppos hp1 hVpos hEpos hfrobS hVfrob
    -- align the lam in hbs (it uses min(√(q/(2V)), p/E)) with our lam = same.
    calc 2 * ((q:ℝ) / (lam * Real.exp 1)) ^ (q:ℝ) * Real.exp (V * lam^2)
        = 2 * ((q:ℝ) / (Real.exp 1 * lam)) ^ (q:ℝ) * Real.exp (lam^2 * V) := by
          rw [mul_comm lam (Real.exp 1), mul_comm V (lam^2)]
      _ ≤ (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ (q:ℝ) := by
          rw [hlam]; exact hbs
      _ = (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ q := by
          rw [Real.rpow_natCast]
end NeumannDependency7
export NeumannDependency7 (scalar_centered_sampling_qnorm_rosenthal_estimate)

-- Accepted proof by Aphrodite; submission 6de2815a-d3a1-4bb4-a454-6ae919754d29.
-- Original source SHA-256: b5d8af983d064e499458ab023a316144d4a6d86f329ffe1869c77ef1fc3b968f.
namespace NeumannDependency8
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

namespace Prove75459

variable {n₁ n₂ : ℕ}

/-- `e^{-q} ≤ n^{-β}` whenever `q ≥ β·log n` and `n ≥ 1`. -/
theorem exp_neg_le_rpow_neg (n β : ℝ) (hn : 1 ≤ n) (q : ℝ)
    (hq : β * Real.log n ≤ q) : Real.exp (-q) ≤ Real.rpow n (-β) := by
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hr : Real.rpow n (-β) = Real.exp (Real.log n * (-β)) := Real.rpow_def_of_pos hnpos _
  rw [hr, Real.exp_le_exp]; nlinarith [hq]

/-- `√(q/p) ≤ (q/bl)·√(bl/p)` for `q ≥ bl > 0`, `p > 0`. -/
theorem sqrt_ratio_le (p bl q : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q) :
    Real.sqrt (q/p) ≤ (q/bl) * Real.sqrt (bl/p) := by
  have hqpos0 : 0 < q := lt_of_lt_of_le hbl hq
  rw [show (q/bl) * Real.sqrt (bl/p) = Real.sqrt ((q/bl)^2 * (bl/p)) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [show (q/bl)^2 * (bl/p) = q^2 / (bl * p) by field_simp]
  rw [div_le_div_iff₀ hp (by positivity)]
  have hqpos : 0 < q := lt_of_lt_of_le hbl hq
  nlinarith [hq, hbl, hp, hqpos, mul_le_mul_of_nonneg_right hq (le_of_lt hqpos)]

/-- The inner factor comparison `J(q) ≤ (q/bl)·M`. -/
theorem inner_ratio_le (p bl q F E : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q)
    (hF : 0 ≤ F) (hE : 0 ≤ E) :
    Real.sqrt (q/p) * F + (q/p) * E ≤ (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by
  have h1 : Real.sqrt (q/p) * F ≤ (q/bl) * (Real.sqrt (bl/p) * F) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sqrt_ratio_le p bl q hp hbl hq) hF
  have h2 : (q/p) * E ≤ (q/bl) * ((bl/p) * E) := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hE
    rw [div_mul_div_comm, div_le_div_iff₀ hp (by positivity)]
    have hqpos : 0 < q := lt_of_lt_of_le hbl hq
    nlinarith [hq, hbl, hp, hqpos]
  calc Real.sqrt (q/p) * F + (q/p) * E
      ≤ (q/bl) * (Real.sqrt (bl/p) * F) + (q/bl) * ((bl/p) * E) := add_le_add h1 h2
    _ = (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by ring

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The Bernoulli observation weights sum to 1. -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const, Finset.card_compl]

/-- Degeneracy at `p = 0`: the fluctuation is identically `0`, so the moment vanishes. -/
theorem moment_zero_of_p_zero (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin n₁ × Fin n₂),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B)) :
    bernoulliExpectation (0:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  have hzero : ∀ Omega : Finset (Fin n₁ × Fin n₂), Coeff Omega = 0 := by
    intro Omega; rw [hCoeff]
    unfold matrixEntrySum centeredSamplingFluctuation
    simp [inv_zero]
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only [hzero, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]

/-- Degeneracy at `n₁ = n₂ = 1`, `p = 1`: the fluctuation vanishes on the full set
and the empty set carries weight `0`, so the moment vanishes. -/
theorem moment_zero_of_n_one (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin 1 × Fin 1) → ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin 1 × Fin 1),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B)) :
    bernoulliExpectation (1:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only []
  have hsingle : ∀ x : Fin 1 × Fin 1, x = (0,0) := by
    intro x; obtain ⟨a, b⟩ := x; fin_cases a <;> fin_cases b <;> rfl
  by_cases hmem : (0,0) ∈ Omega
  · have huniv : Omega = Finset.univ :=
      Finset.eq_univ_of_forall (fun x => by rw [hsingle x]; exact hmem)
    have hC0 : Coeff Omega = 0 := by
      rw [hCoeff]
      unfold matrixEntrySum
      refine Finset.sum_eq_zero (fun w _ => ?_)
      show (1:ℝ)⁻¹ * ((samplingProjection Omega B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
      simp [samplingProjection, huniv]
    simp only [hC0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
  · have hempty : Omega = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩; rw [hsingle x] at hx; exact hmem hx
    have hw : bernoulliObservationWeight (1:ℝ) Omega = 0 := by
      rw [hempty]; unfold bernoulliObservationWeight; simp
    rw [hw, zero_mul]

end Prove75459

open Prove75459 in
/-- `scalar_centered_sampling_qmoment_bernstein_estimate` (75459b07) as a reduction
onto the Rosenthal/Bernstein q-norm core
`scalar_centered_sampling_qnorm_rosenthal_estimate`. See the q-norm node for the
sourced statement (Rosenthal 1970; Boucheron–Lugosi–Massart Ch. 15;
Candès–Recht arXiv:0805.4471 §6).

Choose `q = ⌈β·log(max n₁ n₂)⌉`. For `max n₁ n₂ ≥ 2` and `p > 0`,
`bl := β·log n > β·log 2 > 1` (as `β > 2`), so `bl ≤ q ≤ 2·bl` and the core's inner
factor `J(q) ≤ (q/bl)·M ≤ 2·M`. With `Cbern = 2·e·C`, `cbern = 1`,
`E|Coeff|^q ≤ (C·J(q))^q ≤ (2C·M)^q ≤ (Cbern·M)^q·e^{-q} ≤ (Cbern·M)^q·n^{-β}`.
The degenerate cases `p = 0` (`m = 0`) and `n₁ = n₂ = 1` (`p ∈ {0,1}`) give
`E|Coeff|^q = 0 = RHS`. -/
theorem scalar_centered_sampling_qmoment_bernstein_estimate :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∃ q : ℕ, 1 ≤ q ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (Cbern *
                (Real.sqrt
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((β * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q *
              (cbern * Real.rpow (↑(max n₁ n₂)) (-β)) := by
  obtain ⟨C, hCpos, hcore⟩ := scalar_centered_sampling_qnorm_rosenthal_estimate
  refine ⟨2 * Real.exp 1 * C, 1, by positivity, one_pos, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set nn : ℝ := (↑(max n₁ n₂) : ℝ) with hnn
  set bl : ℝ := β * Real.log nn with hbl
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hnn1 : 1 ≤ nn := by rw [hnn]; exact_mod_cast hmaxpos
  have hnnpos : 0 < nn := lt_of_lt_of_le one_pos hnn1
  have hentrySN_nn : 0 ≤ entrySupNorm B :=
    Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hE_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hF_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob
  -- failProb ≥ 0
  have hrpow_nn : 0 ≤ Real.rpow nn (-β) := le_of_lt (Real.rpow_pos_of_pos hnnpos _)
  -- Degenerate case p = 0
  by_cases hpz : p = 0
  · refine ⟨1, le_refl 1, ?_⟩
    have hcoeff0 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B) := by
      intro Omega; rw [hCoeff, hpz]
    have hmom0 := moment_zero_of_p_zero (n₁ := n₁) (n₂ := n₂) 1 (le_refl 1) Coeff B hcoeff0
    rw [hpz, hmom0]
    -- RHS = 0 since bl/0 = 0 ⇒ inner = 0
    simp only [div_zero, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
  · -- p > 0
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    by_cases hmax1 : max n₁ n₂ = 1
    · -- n₁ = n₂ = 1, p ∈ {0,1}, and p > 0 forces p = 1
      have hn1e : n₁ = 1 := by omega
      have hn2e : n₂ = 1 := by omega
      subst hn1e; subst hn2e
      -- p = m / 1 = m, and m ≤ 1, m > 0 (else p = 0), so m = 1, p = 1
      have hpm : p = (m : ℝ) := by rw [hp]; norm_num
      have hmpos : 0 < m := by
        by_contra h; push_neg at h; interval_cases m; simp [hpm] at hppos
      have hm1 : m = 1 := by omega
      have hpeq1 : p = 1 := by rw [hpm, hm1]; norm_num
      refine ⟨1, le_refl 1, ?_⟩
      have hcoeff1 : ∀ Omega : Finset (Fin 1 × Fin 1),
          Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B) := by
        intro Omega; rw [hCoeff, hpeq1]
      have hmom0 := moment_zero_of_n_one 1 (le_refl 1) Coeff B hcoeff1
      have hbl0 : bl = 0 := by
        rw [hbl, hnn]; norm_num
      rw [hpeq1, hmom0, hbl0]
      simp only [zero_div, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
    · -- main case: max n₁ n₂ ≥ 2, p > 0
      have hmax2 : 2 ≤ max n₁ n₂ := by omega
      have hnn2 : 2 ≤ nn := by rw [hnn]; exact_mod_cast hmax2
      have hlog2 : Real.log 2 ≤ Real.log nn := Real.log_le_log (by norm_num) hnn2
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hblpos : 0 < bl := by
        rw [hbl]; exact mul_pos (by linarith) (lt_of_lt_of_le hlog2pos hlog2)
      have hbl1 : 1 < bl := by
        rw [hbl]
        have hstep : (2:ℝ) * Real.log 2 ≤ β * Real.log nn := by
          apply le_trans (le_of_lt (mul_lt_mul_of_pos_right hβ hlog2pos))
          exact mul_le_mul_of_nonneg_left hlog2 (by linarith)
        nlinarith [Real.log_two_gt_d9, hstep, hlog2pos]
      -- choose q = ⌈bl⌉
      set q : ℕ := ⌈bl⌉₊ with hqdef
      have hqge : bl ≤ (q : ℝ) := Nat.le_ceil bl
      have hqle : (q : ℝ) ≤ bl + 1 := by
        rw [hqdef]; exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt hblpos))
      have hq1 : 1 ≤ q := by
        rw [hqdef]; exact Nat.one_le_ceil_iff.mpr hblpos
      have hq2bl : (q : ℝ) ≤ 2 * bl := by nlinarith [hqge, hqle, hbl1]
      have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
      refine ⟨q, hq1, ?_⟩
      -- the core bound
      have hc := hcore n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob q hq1
      rw [← hp] at hc
      -- abbreviations for inner factors
      set M : ℝ := Real.sqrt (bl/p) * frobScale + (bl/p) * entryScale with hM
      set J : ℝ := Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale with hJ
      -- hc : bernoulliExpectation p (|Coeff|^q) ≤ (C * J)^q
      -- step 1: J ≤ (q/bl) * M ≤ 2 * M
      have hJM : J ≤ (q/bl) * M := by
        rw [hJ, hM]; exact inner_ratio_le p bl q frobScale entryScale hppos hblpos hqge hF_nn hE_nn
      have hMnn : 0 ≤ M := by
        rw [hM]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn
      have hqblle2 : (q:ℝ)/bl ≤ 2 := by rw [div_le_iff₀ hblpos]; linarith [hq2bl]
      have hJ2M : J ≤ 2 * M := by
        refine le_trans hJM ?_
        have := mul_le_mul_of_nonneg_right hqblle2 hMnn
        linarith [this]
      have hJnn : 0 ≤ J := by
        rw [hJ]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn
      -- step 2: (C*J)^q ≤ (C*(2*M))^q = (2*C*M)^q
      have hstep2 : (C * J)^q ≤ (2 * C * M)^q := by
        apply pow_le_pow_left₀ (by positivity)
        calc C * J ≤ C * (2 * M) := by
              exact mul_le_mul_of_nonneg_left hJ2M (le_of_lt hCpos)
          _ = 2 * C * M := by ring
      -- step 3: (2*C*M)^q ≤ (Cbern*M)^q * n^{-β}, Cbern = 2*e*C
      -- (Cbern*M)^q * n^{-β} = (2*e*C*M)^q * n^{-β} = (2*C*M)^q * e^q * n^{-β}
      have hexp : Real.exp (-(q:ℝ)) ≤ Real.rpow nn (-β) :=
        exp_neg_le_rpow_neg nn β hnn1 q (le_trans hqge (le_refl _))
      have hexpq_pos : 0 < Real.exp 1 ^ q := by positivity
      have h2CM_nn : 0 ≤ (2 * C * M)^q := by positivity
      have hfac : 1 ≤ (Real.exp 1)^q * Real.rpow nn (-β) := by
        have hee : (Real.exp 1)^q = Real.exp (q:ℝ) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [hee]
        calc (1:ℝ) = Real.exp (q:ℝ) * Real.exp (-(q:ℝ)) := by
              rw [← Real.exp_add]; simp
          _ ≤ Real.exp (q:ℝ) * Real.rpow nn (-β) :=
              mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.exp_pos _))
      have hstep3 : (2 * C * M)^q ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := by
        have hbase : (2 * Real.exp 1 * C * M)^q = (2 * C * M)^q * (Real.exp 1)^q := by
          rw [← mul_pow]; congr 1; ring
        have hrw : (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β))
            = (2 * C * M)^q * ((Real.exp 1)^q * Real.rpow nn (-β)) := by
          rw [hbase, one_mul, mul_assoc]
        rw [hrw]
        exact le_mul_of_one_le_right h2CM_nn hfac
      -- combine
      calc bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
          ≤ (C * J)^q := hc
        _ ≤ (2 * C * M)^q := hstep2
        _ ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := hstep3
end NeumannDependency8
export NeumannDependency8 (scalar_centered_sampling_qmoment_bernstein_estimate)

-- Accepted proof by Aphrodite; submission 03ca17ec-8750-4cd9-a80a-9e54a267d3ea.
-- Original source SHA-256: f3af4dceb03e74479f1b0af3335b16d58781c105d0abbff2be63a90c0d4d4fb5.
namespace NeumannDependency9
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

namespace ProveMarkov

variable {n₁ n₂ : ℕ}

/-- The Bernoulli observation weights sum to 1 (a probability measure on the
powerset of entries), for any real `p` (binomial theorem). -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- Probability of an event plus its complement is `1`. -/
theorem prob_add_compl (p : ℝ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event +
      bernoulliEventProb p (fun Omega => ¬ Event Omega) = 1 := by
  classical
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib, ← weights_sum_one (n₁ := n₁) (n₂ := n₂) p]
  apply Finset.sum_congr rfl
  intro Omega _
  by_cases h : Event Omega <;> simp [h]

end ProveMarkov

open ProveMarkov in
/-- `scalar_centered_sampling_markov_tail_from_qmoment_bound`.
Markov's inequality on the finite Bernoulli observation measure: if the `q`-th
absolute moment of a scalar statistic `Z` is at most `t^q · failProb`, then `Z`
stays within `t` with probability at least `1 - failProb`. -/
theorem scalar_centered_sampling_markov_tail_from_qmoment_bound
    {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (t failProb : ℝ) (ht : 0 < t) (hfail : 0 ≤ failProb)
    (hmoment : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ t ^ q * failProb) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) ≥ 1 - failProb := by
  classical
  set Bad : Finset (Fin n₁ × Fin n₂) → Prop := fun Omega => ¬ (|Z Omega| ≤ t) with hBad
  have htq : (0:ℝ) < t ^ q := by positivity
  have hkey : t ^ q * bernoulliEventProb p Bad ≤
      bernoulliExpectation p (fun Omega => |Z Omega| ^ q) := by
    unfold bernoulliEventProb bernoulliExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Omega _
    by_cases h : Bad Omega
    · simp only [h, if_true]
      have hlt : t < |Z Omega| := by rw [hBad] at h; push_neg at h; exact h
      have hpow : t ^ q ≤ |Z Omega| ^ q :=
        pow_le_pow_left₀ (le_of_lt ht) (le_of_lt hlt) q
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      calc t ^ q * bernoulliObservationWeight p Omega
          = bernoulliObservationWeight p Omega * t ^ q := by ring
        _ ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
              mul_le_mul_of_nonneg_left hpow hw
    · simp only [h, if_false, mul_zero]
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      positivity
  have hPbad : bernoulliEventProb p Bad ≤ failProb := by
    have h1 : t ^ q * bernoulliEventProb p Bad ≤ t ^ q * failProb :=
      le_trans hkey hmoment
    exact le_of_mul_le_mul_left h1 htq
  have hsplit : bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) +
      bernoulliEventProb p Bad = 1 := by
    have := prob_add_compl (n₁ := n₁) (n₂ := n₂) p (fun Omega => |Z Omega| ≤ t)
    rw [hBad]; exact this
  linarith [hPbad, hsplit]
end NeumannDependency9
export NeumannDependency9 (scalar_centered_sampling_markov_tail_from_qmoment_bound)

-- Accepted proof by Aphrodite; submission 0b5156fe-a2eb-4ccc-8893-87aa851fcc00.
-- Original source SHA-256: 69759f1182e011602b3a15ea6c9a1eb39c1812855a700e70fea2fa933ff1deb4.
namespace NeumannDependency10
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

namespace Prove3cbb

variable {n₁ n₂ : ℕ}

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The Bernoulli observation weights sum to 1. -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

/-- Edge case `t = 0`: if the `q`-moment is `0`, the event `|Z| ≤ 0` has prob ≥ 1 - failProb. -/
theorem tail_at_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (failProb : ℝ) (hfail : 0 ≤ failProb)
    (hmom0 : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ 0) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0) ≥ 1 - failProb := by
  classical
  -- each term w(Ω) * |Z Ω|^q ≥ 0, and the sum ≤ 0, so each term = 0
  have hterm_nn : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q := by
    intro Omega
    have := weight_nonneg (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Omega
    positivity
  have hsum0 : ∑ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have hge : (0:ℝ) ≤ ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
      Finset.sum_nonneg (fun Omega _ => hterm_nn Omega)
    have hle : (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q) ≤ 0 := by
      unfold bernoulliExpectation at hmom0; exact hmom0
    linarith
  have heach : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun Omega _ => hterm_nn Omega)).1 hsum0
    intro Omega; exact h Omega (Finset.mem_univ _)
  -- For Ω with Z Ω ≠ 0, weight is 0; so prob of |Z|≤0 = sum over all = 1
  have hbe : bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0)
      = ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl
    intro Omega _
    by_cases h : |Z Omega| ≤ 0
    · simp [h]
    · -- |Z Ω| > 0 ⇒ |Z Ω|^q > 0 ⇒ weight = 0
      push_neg at h
      have hZpos : 0 < |Z Omega| := h
      have hpowpos : 0 < |Z Omega| ^ q := by positivity
      have hw0 : bernoulliObservationWeight p Omega = 0 := by
        have := heach Omega
        rcases mul_eq_zero.1 this with h1 | h2
        · exact h1
        · exact absurd h2 (ne_of_gt hpowpos)
      simp [h, hw0]
  rw [hbe, weights_sum_one]
  linarith

end Prove3cbb

open Prove3cbb in
/-- `scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales` (3cbb6b11)
as a reduction onto the q-moment Bernstein core
`scalar_centered_sampling_qmoment_bernstein_estimate` and the proved Markov-tail
node `scalar_centered_sampling_markov_tail_from_qmoment_bound` (74ed00ae). -/
theorem scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                Cbern *
                  (Real.sqrt
                      ((β * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    frobScale +
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entryScale)) ≥
          1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cbern, cbern, hCbern, hcbern, hcore⟩ :=
    scalar_centered_sampling_qmoment_bernstein_estimate
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn
  set T : ℝ := Cbern *
      (Real.sqrt ((β * Real.log n) / p) * frobScale +
        ((β * Real.log n) / p) * entryScale) with hT
  set failProb : ℝ := cbern * Real.rpow n (-β) with hfp
  -- p ∈ [0,1]
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by
    rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    rw [div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  -- failProb ≥ 0
  have hnpos : (0:ℝ) < n := by
    rw [hn]; have : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _); exact_mod_cast this
  have hfail : 0 ≤ failProb := by
    rw [hfp]; apply mul_nonneg (le_of_lt hcbern); exact le_of_lt (Real.rpow_pos_of_pos hnpos _)
  -- get the moment bound from the core
  obtain ⟨q, hq, hmoment⟩ := hcore β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  -- fold the abbreviations into the obtained moment bound
  rw [← hp, ← hn, ← hT, ← hfp] at hmoment
  -- hmoment : bernoulliExpectation p (|Coeff|^q) ≤ T^q * failProb
  -- T ≥ 0
  have hlogn_nn : 0 ≤ Real.log n := by
    rw [hn]
    apply Real.log_nonneg
    have : 1 ≤ max n₁ n₂ := le_trans hn1 (le_max_left _ _)
    exact_mod_cast this
  have hbeta_log_nn : 0 ≤ β * Real.log n := mul_nonneg (by linarith) hlogn_nn
  have hbl_div_nn : 0 ≤ (β * Real.log n) / p := div_nonneg hbeta_log_nn hp0
  -- entrySupNorm, frobeniusNorm are nonneg, so the scales are nonneg
  have hentrySN_nn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    apply Real.iSup_nonneg
    intro i
    apply Real.iSup_nonneg
    intro j
    exact abs_nonneg _
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hentry_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hfrob_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob
  have hbracket_nn : 0 ≤ Real.sqrt ((β * Real.log n) / p) * frobScale +
      ((β * Real.log n) / p) * entryScale := by
    apply add_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) hfrob_nn
    · exact mul_nonneg hbl_div_nn hentry_nn
  have hT_nn : 0 ≤ T := by rw [hT]; exact mul_nonneg (le_of_lt hCbern) hbracket_nn
  -- (goal already folded into T / failProb by `set`)
  -- case split on T = 0 vs T > 0
  rcases eq_or_lt_of_le hT_nn with hT0 | hTpos
  · -- T = 0 edge: moment ≤ T^q * failProb = 0
    have hTeq : T = 0 := hT0.symm
    have hTq0 : T ^ q = 0 := by rw [hTeq]; exact zero_pow (by omega)
    have hmom0 : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q) ≤ 0 := by
      rw [hTq0, zero_mul] at hmoment; exact hmoment
    -- the target event |Coeff| ≤ T = 0
    have hres := tail_at_zero (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Coeff q hq failProb hfail hmom0
    rw [hTeq]; exact hres
  · -- T > 0: apply the Markov tail node
    exact scalar_centered_sampling_markov_tail_from_qmoment_bound p hp0 hp1 Coeff q hq
      T failProb hTpos hfail hmoment
end NeumannDependency10
export NeumannDependency10 (scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales)

-- Accepted proof by Minghui; submission c7dbc859-548a-4a67-b166-87671b96b50e.
-- Original source SHA-256: 6349c10d33376b0a0c0d6ae9fc4e037629caba1b8becab5254595332395297a2.
namespace NeumannDependency11
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint *
                    (Real.sqrt
                        ((β * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Cfro * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      ((β * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                        (Centry * μ₁ *
                          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hCentry _hCfrob
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hbern⟩
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1
    hrepr hentry hfrob w1 w2
  exact
    hbern β hβ n₁ n₂ m hn₁ hn₂ hm
      (fun Omega3 =>
        quadraticAllDistinctInnerCoefficient Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2)
      (quadraticAllDistinctInnerBaseMatrix S w1 w2)
      (Centry * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
      (Cfro * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
      (by
        intro Omega3
        exact hrepr Omega3 w1 w2)
      (hentry w1 w2)
      (hfrob w1 w2)
end NeumannDependency11
export NeumannDependency11 (quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim)

-- Accepted proof by Shuze Chen; submission e787da7e-35db-4239-8024-f952c3fcfd5a.
-- Original source SHA-256: 0ff846f4d3bd80f32329b8df89f3172b6733920c97e1211dc14fa707704dfb68.
namespace NeumannDependency12
open MatrixCompletion
open scoped Classical BigOperators

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

/-- The A1 incoherence assumption gives the entry-sup norm bound for the sign
matrix. -/
theorem entry_sup_norm_sign_matrix_bound_from_a1
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (μ₁ : ℝ) (S : SVD M r) :
    A1 S μ₁ →
    entrySupNorm (signMatrix S) ≤
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  intro hA1
  exact entrySupNorm_le_of_forall_abs_le hn₁ hn₂ (signMatrix S) _ hA1
end NeumannDependency12
export NeumannDependency12 (entry_sup_norm_sign_matrix_bound_from_a1)

-- Accepted proof by Shuze Chen; submission 45b3328d-181c-48a8-ba09-2a2b2d50ad63.
-- Original source SHA-256: 20f6feb0a7e1e053cc878e2f632896fc5081c48828c54f7fca23af1a0754d622.
namespace NeumannDependency13
open MatrixCompletion

open scoped Classical BigOperators

private lemma coherence_coordinate_energy_le
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} :
    coherence N r u ≤ μ →
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro hcoh i
  have hscale_pos : 0 < (N : ℝ) / (r : ℝ) :=
    div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hr)
  have hleSup :
      (∑ k : Fin r, (u k i) ^ 2) ≤
        ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 :=
    Finite.le_ciSup (f := fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hsup :
      (⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2) ≤
        μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hscale_pos]
    simpa [coherence, mul_comm, mul_left_comm, mul_assoc] using hcoh
  calc
    (∑ k : Fin r, (u k i) ^ 2)
        ≤ μ / ((N : ℝ) / (r : ℝ)) := le_trans hleSup hsup
    _ = μ * (r : ℝ) / (N : ℝ) := by
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      field_simp [hN', hr']

/-- A0 is exactly a pair of coherence bounds, and unfolding coherence gives
the pointwise coordinate-energy estimates. -/
theorem a0_singular_coordinate_energy_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → A0 S μ₀ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
  intro hn₁ hn₂ hr hA0
  exact ⟨coherence_coordinate_energy_le hn₁ hr S.u hA0.1,
    coherence_coordinate_energy_le hn₂ hr S.v hA0.2⟩
end NeumannDependency13
export NeumannDependency13 (a0_singular_coordinate_energy_bounds)

-- Accepted proof by Shuze Chen; submission 8c6ec413-f104-42e3-8c17-021140b35019.
-- Original source SHA-256: 3778ee094727d3f6884a3a8ecf43d9a2a97f2a0f14122a9d345db6938e4e10ce.
namespace NeumannDependency14
open MatrixCompletion

open scoped Classical BigOperators

private lemma coordinate_energy_le_one_of_orthonormal
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0) :
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ (1 : ℝ) := by
  intro i
  let P : Fin N → ℝ := fun a => ∑ k : Fin r, u k i * u k a
  have hP_nonneg : 0 ≤ P i := by
    dsimp [P]
    exact Finset.sum_nonneg fun k _ => by nlinarith [sq_nonneg (u k i)]
  have hsum_idem : ∑ a : Fin N, (P a) ^ 2 = P i := by
    calc
      ∑ a : Fin N, (P a) ^ 2
          = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
              (u k i * u l i) * (u k a * u l a) := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro a _ha
            simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            ring
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _hl
            rw [Finset.mul_sum]
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (if k = l then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            rw [horth k l]
      _ = ∑ k : Fin r, (u k i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_eq_single k]
            · simp [pow_two]
            · intro l _hl hne
              have hkne : k ≠ l := fun h => hne h.symm
              simp [hkne]
            · intro hnot
              exact (hnot (Finset.mem_univ k)).elim
      _ = P i := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  have hsq_le_sum : (P i) ^ 2 ≤ ∑ a : Fin N, (P a) ^ 2 := by
    exact Finset.single_le_sum (fun a _ha => sq_nonneg (P a)) (Finset.mem_univ i)
  have hsq_le : (P i) ^ 2 ≤ P i := by
    simpa [hsum_idem] using hsq_le_sum
  have hPi_le_one : P i ≤ (1 : ℝ) := by
    nlinarith
  simpa [P, pow_two] using hPi_le_one

/-- Bessel's inequality for the finite orthonormal singular-vector families in
the explicit `SVD` structure. -/
theorem svd_singular_coordinate_energy_le_one
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
      (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) ∧
      (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) := by
  exact ⟨coordinate_energy_le_one_of_orthonormal S.u S.u_orthonormal,
    coordinate_energy_le_one_of_orthonormal S.v S.v_orthonormal⟩
end NeumannDependency14
export NeumannDependency14 (svd_singular_coordinate_energy_le_one)

-- Accepted proof by Shuze Chen; submission 40ff5466-567e-4318-a3a3-0a46be82efe9.
-- Original source SHA-256: 8a7f4f14f792b041339d362229978150c2df0a86686559b0e7f56a17e76ce6a1.
namespace NeumannDependency15
open MatrixCompletion

open scoped Classical BigOperators

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma leftSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.u k i) ^ 2 := by
  unfold leftSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma rightSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.v k j) ^ 2 := by
  unfold rightSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single j]
  · simp [pow_two]
  · intro b _hb hb
    simp [hb]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private lemma twoSidedSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) i j =
      (∑ k : Fin r, (S.u k i) ^ 2) *
        (∑ k : Fin r, (S.v k j) ^ 2) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [pow_two, Finset.mul_sum, Finset.sum_mul]
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection, leftSingularProjection_coordinate_same,
    rightSingularProjection_coordinate_same,
    twoSidedSingularProjection_coordinate_same]

/-- The diagonal tangent-kernel estimate follows from coordinate-energy bounds
for the two singular-vector spaces and the Bessel bounds that those energies
are at most one. -/
theorem tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨3, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hu hv huOne hvOne i j
  let U : ℝ := ∑ k : Fin r, (S.u k i) ^ 2
  let V : ℝ := ∑ k : Fin r, (S.v k j) ^ 2
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hU_one : U ≤ 1 := by
    simpa [U] using huOne i
  have hV_one : V ≤ 1 := by
    simpa [V] using hvOne j
  have hU_scale : U ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
      exact_mod_cast min_le_left n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [U] using hu i) hmono
  have hV_scale : V ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
      exact_mod_cast min_le_right n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [V] using hv j) hmono
  have hformula := tangent_coordinate_kernel_diagonal_formula S i j
  have hnonneg_expr : 0 ≤ U + V - U * V := by
    have h1V : 0 ≤ 1 - V := by linarith
    nlinarith [mul_nonneg hU_nonneg h1V, hV_nonneg]
  calc
    |tangentCoordinateKernel S i j i j|
        = |U + V - U * V| := by
          rw [hformula]
    _ = U + V - U * V := abs_of_nonneg hnonneg_expr
    _ ≤ U + V := by nlinarith [mul_nonneg hU_nonneg hV_nonneg]
    _ ≤ scale + scale := by linarith
    _ ≤ 3 * scale := by nlinarith [hscale_nonneg]
    _ = 3 * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      dsimp [scale]
      ring
end NeumannDependency15
export NeumannDependency15 (tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies)

-- Accepted proof by Shuze Chen; submission 2c080235-8f92-4443-97fc-a123dbba4860.
-- Original source SHA-256: d4224fd87abb0100a16ff7c9215d4149ec311382a081984ce02b65b1c2cd7bf8.
namespace NeumannDependency16
open MatrixCompletion

open scoped Classical BigOperators

/--
Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), together with the
rectangular-scale convention stated after PDF p. 24, estimates (6.2)--(6.4).

Estimate (6.2) bounds the diagonal tangent-coordinate kernel by the incoherence
scale.  The reduction separates the finite-dimensional proof into three parts:
A0 gives coordinate-energy bounds for the left and right singular-vector
families, orthonormality gives the Bessel bounds that each such coordinate
energy is at most one, and the remaining child converts those energy estimates
into the diagonal tangent-kernel bound at scale `μ₀ r / min(n₁,n₂)`.
-/
theorem tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies with
    ⟨Cker, hCker_pos, hker⟩
  refine ⟨Cker, hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  have hEnergy :=
    a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  exact hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀
    hEnergy.1 hEnergy.2 hOne.1 hOne.2 i j
end NeumannDependency16
export NeumannDependency16 (tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim)

-- Accepted proof by LukeBernese; submission e6cda329-7049-43de-952b-3da179d9fdae.
-- Original source SHA-256: e44edf000d5e30899486ed9a9596b847ef2d8ad847c8203cc024556cfce460c5.
namespace NeumannDependency17
open MatrixCompletion
open scoped BigOperators

namespace MatrixCompletion

/-! ## matrixInner linearity helpers -/

theorem matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem matrixInner_add_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y + Z) = matrixInner X Y + matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]

theorem matrixInner_sub_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.sub_apply, mul_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]

theorem matrixInner_zero_right {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X 0 = 0 := by
  unfold matrixInner
  simp

/-! ## Generic kernel self-adjointness

Every projection `P` here has the form `(P X) i j = ∑ a, ∑ b, K i j a b * X a b`
for a kernel `K` with the symmetry `K i j a b = K a b i j`.  Such a `P` is
self-adjoint for `matrixInner`. -/

-- Swap the outer index pair (i,j) with the inner index pair (a,b) in a 4-fold sum.
private theorem sum_pair_collapse {n1 n2 : Nat}
    (G : Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, G i j)
      = ∑ p : Fin n1 × Fin n2, G p.1 p.2 := by
  rw [← Finset.sum_product']
  rfl

private theorem sum4_swap {n1 n2 : Nat}
    (F : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) = (∑ a, ∑ b, ∑ i, ∑ j, F i j a b) := by
  have h1 : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
      = ∑ p : Fin n1 × Fin n2, ∑ q : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun i j => ∑ a, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [sum_pair_collapse (fun a b => F p.1 p.2 a b)]
  have h2 : (∑ a, ∑ b, ∑ i, ∑ j, F i j a b)
      = ∑ q : Fin n1 × Fin n2, ∑ p : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun a b => ∑ i, ∑ j, F i j a b)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [sum_pair_collapse (fun i j => F i j q.1 q.2)]
  rw [h1, h2, Finset.sum_comm]

theorem matrixInner_kernel_selfAdjoint {n1 n2 : Nat}
    (K : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real)
    (hK : ∀ i j a b, K i j a b = K a b i j)
    (X Y : RealMatrix n1 n2) :
    matrixInner (fun i j => ∑ a, ∑ b, K i j a b * X a b) Y
      = matrixInner X (fun i j => ∑ a, ∑ b, K i j a b * Y a b) := by
  unfold matrixInner
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- LHS: ∑ i ∑ j ∑ a ∑ b, K i j a b * X a b * Y i j
  -- RHS: ∑ i ∑ j ∑ a ∑ b, X i j * (K i j a b * Y a b)
  -- Swap (i,j)<->(a,b) on the RHS, then match termwise via hK.
  rw [sum4_swap (fun i j a b => X i j * (K i j a b * Y a b))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hK a b i j]
  ring

/-! ## Self-adjointness of each projection, via the generic kernel lemma -/

theorem leftSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (leftSingularProjection S X) Y = matrixInner X (leftSingularProjection S Y) := by
  have hL : ∀ (Z : RealMatrix n1 n2),
      leftSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((∑ k, S.u k i * S.u k a) * (if b = j then 1 else 0)) * Z a b) := by
    intro Z
    funext i j
    unfold leftSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hL X, hL Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hbj : b = j <;> by_cases hji : j = b
  · subst hbj; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hbj; exact absurd rfl hji
  · exact absurd hji.symm hbj
  · simp [hbj, fun h : j = b => hji h]

theorem rightSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (rightSingularProjection S X) Y = matrixInner X (rightSingularProjection S Y) := by
  have hR : ∀ (Z : RealMatrix n1 n2),
      rightSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((if a = i then 1 else 0) * (∑ k, S.v k b * S.v k j)) * Z a b) := by
    intro Z
    funext i j
    unfold rightSingularProjection
    -- LHS: ∑ b, Z i b * d b j ;  RHS: ∑ a ∑ b ((if a=i then 1 else 0)*d b j)*Z a b
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_); simp; ring
    · intro a _ ha; refine Finset.sum_eq_zero (fun b _ => ?_); simp [ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hR X, hR Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hai : a = i <;> by_cases hia : i = a
  · subst hai; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hai; exact absurd rfl hia
  · exact absurd hia.symm hai
  · simp [hai, fun h : i = a => hia h]

theorem twoSidedSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S X) Y
      = matrixInner X (twoSidedSingularProjection S Y) := by
  have hT : ∀ (Z : RealMatrix n1 n2),
      twoSidedSingularProjection S Z
        = (fun i j => ∑ a, ∑ b,
            ((∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j)) * Z a b) := by
    intro Z
    funext i j
    unfold twoSidedSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hT X, hT Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  -- K i j a b = (∑k u k i u k a)(∑l v l b v l j); K a b i j = (∑k u k a u k i)(∑l v l j v l i)... careful
  -- Actually K a b i j = (∑k u k a u k i)(∑l v l j v l b)
  have hu : (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    refine Finset.sum_congr rfl (fun k _ => ?_); ring
  have hv : (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    refine Finset.sum_congr rfl (fun l _ => ?_); ring
  rw [hu, hv]

/-! ## Projector idempotency from orthonormality

`Pu i a = ∑ k, u k i * u k a` is the column-space projector; it is idempotent:
`∑ a', Pu i a' * Pu a' a = Pu i a`.  Same for `Pv`. -/

-- ∑ c ∑ k ∑ l F c k l = ∑ k ∑ l ∑ c F c k l (move first index innermost).
private theorem sum3_rot {γ κ μ : Type*} [Fintype γ] [Fintype κ] [Fintype μ]
    (F : γ → κ → μ → Real) :
    (∑ c, ∑ k, ∑ l, F c k l) = ∑ k, ∑ l, ∑ c, F c k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

private theorem u_proj_idem {n1 r : Nat} (u : Fin r → (Fin n1 → Real))
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (i a : Fin n1) :
    (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a)) = ∑ k, u k i * u k a := by
  have hflat : (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a))
      = ∑ c, ∑ k, ∑ l, (u k i * u l a) * (u k c * u l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (u k i * u l a) * (u k c * u l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (u k i * u l a) * (u k c * u l c))
      = ∑ k, ∑ l, (u k i * u l a) * (∑ c, u k c * u l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hu k k]; simp
  · intro l _ hl; rw [hu k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

private theorem v_proj_idem {n2 r : Nat} (v : Fin r → (Fin n2 → Real))
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (b j : Fin n2) :
    (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j)) = ∑ k, v k b * v k j := by
  have hflat : (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j))
      = ∑ c, ∑ k, ∑ l, (v k b * v l j) * (v k c * v l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (v k b * v l j) * (v k c * v l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (v k b * v l j) * (v k c * v l c))
      = ∑ k, ∑ l, (v k b * v l j) * (∑ c, v k c * v l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hv k k]; simp
  · intro l _ hl; rw [hv k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ## Composition relations of the three projections -/

-- L ∘ L = L
private theorem LL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  -- ∑ a, Pu i a * (∑ a', Pu a a' * X a' j) = ∑ a', Pu i a' * X a' j
  have hflat : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a, ∑ a', (∑ k, S.u k i * S.u k a) * ((∑ k, S.u k a * S.u k a') * X a' j) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  have h1 : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a', (∑ c, (∑ k, S.u k i * S.u k c) * (∑ l, S.u l c * S.u l a')) * X a' j := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [u_proj_idem S.u S.u_orthonormal i a']

-- R ∘ R = R
private theorem RR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hflat : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ b', (X i b' * (∑ k, S.v k b' * S.v k b)) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  have h1 : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b', X i b' * (∑ c, (∑ k, S.v k b' * S.v k c) * (∑ l, S.v l c * S.v l j)) := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [v_proj_idem S.v S.v_orthonormal b' j]

-- L ∘ R = T2  (apply L to (R X))
private theorem LR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  -- ∑ a, Pu i a * (∑ b, X a b * Pv b j) = ∑ a ∑ b, Pu i a * X a b * Pv b j
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

-- R ∘ L = T2
private theorem RL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold rightSingularProjection leftSingularProjection twoSidedSingularProjection
  -- ∑ b, (∑ a, Pu i a * X a b) * Pv b j = ∑ a ∑ b, Pu i a * X a b * Pv b j
  have hflat : (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ a, ((∑ k, S.u k i * S.u k a) * X a b) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  rw [hflat, Finset.sum_comm]

-- T2 = R ∘ L, so by associativity of these compositions we derive the rest.
-- L ∘ T2 = T2 : L (T2 X) = L (L (R X)) = L (R X) = T2 X   (uses LL and LR)
private theorem LT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← LR S X, LL S (rightSingularProjection S X)]

-- T2 ∘ L = T2 : T2 (L X).  T2 = R∘L composition? Actually twoSided applied to (L X).
-- Use T2 X = R (L X) (RL), and T2 (L X) = R (L (L X)) = R (L X) = T2 X.
private theorem T2L {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (leftSingularProjection S X), LL S X, RL S X]

-- R ∘ T2 = T2 : R (T2 X) = R (R (L X)) = R (L X) = T2 X  (uses RL and RR)
private theorem RT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S X, RR S (leftSingularProjection S X)]

-- T2 ∘ R = T2 : T2 (R X) = R (L (R X)) = R (T2 X)... use LR then RT2.
private theorem T2R {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (rightSingularProjection S X), LR S X, RT2 S X]

-- T2 ∘ T2 = T2 : T2 (T2 X) = R (L (T2 X)) = R (T2 X) = T2 X.
private theorem T2T2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (twoSidedSingularProjection S X), LT2 S X, RT2 S X]

/-! ## Linearity of the projections (additive over +, -) -/

private theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem two_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem two_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

/-- `tangentProjection` is additive over subtraction (needed for L3). -/
theorem tangentProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    tangentProjection S (A - B) = tangentProjection S A - tangentProjection S B := by
  unfold tangentProjection
  rw [left_sub, right_sub, two_sub]
  abel

/-! ## L1: self-adjointness of tangentProjection -/

theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (tangentProjection S X) Y = matrixInner X (tangentProjection S Y) := by
  unfold tangentProjection
  -- LHS: inner (L X + R X - T X) Y.  Flip via comm, expand with right-linearity.
  rw [matrixInner_comm (leftSingularProjection S X + rightSingularProjection S X
        - twoSidedSingularProjection S X) Y]
  rw [matrixInner_sub_right, matrixInner_add_right]
  -- RHS: inner X (L Y + R Y - T Y).  Expand with right-linearity.
  rw [matrixInner_sub_right, matrixInner_add_right]
  -- Now LHS: inner Y (LX)+inner Y (RX)-inner Y (TX)
  --     RHS: inner X (LY)+inner X (RY)-inner X (TY)
  rw [matrixInner_comm Y (leftSingularProjection S X),
      matrixInner_comm Y (rightSingularProjection S X),
      matrixInner_comm Y (twoSidedSingularProjection S X)]
  rw [leftSingularProjection_selfAdjoint, rightSingularProjection_selfAdjoint,
      twoSidedSingularProjection_selfAdjoint]

/-! ## L2: idempotency of tangentProjection

`P_T = L + R - T2`.  Using the composition relations
`LL=L, RR=R, LR=RL=T2, L·T2=T2·L=R·T2=T2·R=T2·T2=T2`,
expanding `P_T (P_T X)` gives `L + R - T2 = P_T`. -/

theorem tangentProjection_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- Abbreviate the three projection outputs of X.
  set L := leftSingularProjection S X with hLdef
  set R := rightSingularProjection S X with hRdef
  set T := twoSidedSingularProjection S X with hTdef
  -- P_T (P_T X) = P_T (L + R - T)
  conv_lhs => rw [show tangentProjection S X = L + R - T from rfl]
  unfold tangentProjection
  -- left/right/two of (L + R - T)
  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add]
  -- Now expand each projection-of-a-projection using the composition lemmas.
  rw [hLdef, hRdef, hTdef]
  rw [LL S X, LR S X, LT2 S X,
      RL S X, RR S X, RT2 S X,
      T2L S X, T2R S X, T2T2 S X]
  -- Goal: (L + T2 - T2) + (T2 + R - T2) - (T2 + T2 - T2) = L + R - T2  (as matrices)
  -- where now L,R,T2 are the concrete projections of X. Close by abel.
  abel

/-! ## L3: off-diagonal kernel = tangent-tangent inner product -/

theorem tangentCoordinateKernel_eq_proj_inner {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    tangentCoordinateKernel S i j a b
      = matrixInner (tangentProjection S (coordinateMatrix i j))
          (tangentProjection S (coordinateMatrix a b)) := by
  unfold tangentCoordinateKernel
  -- Write e_ab = P_T e_ab + (e_ab - P_T e_ab).
  have hsplit : (coordinateMatrix a b : RealMatrix n1 n2)
      = tangentProjection S (coordinateMatrix a b)
        + (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) := by
    abel
  conv_lhs => rw [hsplit]
  rw [matrixInner_add_right]
  -- The cross term inner (P_T e_ij) (e_ab - P_T e_ab) = 0.
  have hcross : matrixInner (tangentProjection S (coordinateMatrix i j))
      (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) = 0 := by
    rw [tangentProjection_selfAdjoint S (coordinateMatrix i j)
          (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b))]
    rw [tangentProjection_sub, tangentProjection_idem]
    rw [sub_self, matrixInner_zero_right]
  rw [hcross, add_zero]

/-! ## Base-bound layer (T0–T3)

Cauchy–Schwarz for `matrixInner`, the off-diagonal kernel magnitude bound, and the
entry-sup / Frobenius bounds for the kernel-square base matrix. -/

/-- Probing a matrix with a coordinate matrix reads off the entry. -/
theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The kernel `K(w, ·)` reads off the entries of `P_T e_w`. -/
theorem tangentCoordinateKernel_eq_entry {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (a : Fin n1) (b : Fin n2) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S a b i j
      = (tangentProjection S (coordinateMatrix a b)) i j := by
  unfold tangentCoordinateKernel
  rw [matrixInner_coordinateMatrix]

/-! ### T0: Cauchy–Schwarz for the Frobenius inner product -/

theorem matrixInner_le_frob {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  -- Flatten the double sums to single sums over the product index type.
  have hinner : matrixInner X Y
      = ∑ p : Fin n1 × Fin n2, X p.1 p.2 * Y p.1 p.2 := by
    unfold matrixInner
    rw [← Finset.sum_product']; rfl
  have hX : frobeniusNormSq X = ∑ p : Fin n1 × Fin n2, (X p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl
  have hY : frobeniusNormSq Y = ∑ p : Fin n1 × Fin n2, (Y p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl
  -- Cauchy–Schwarz (squared form).
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    rw [hinner, hX, hY]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin n1 × Fin n2 => X p.1 p.2) (fun p : Fin n1 × Fin n2 => Y p.1 p.2)
  -- Pass to absolute values / square roots.
  have hXnn : 0 ≤ frobeniusNormSq X := by
    rw [hX]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hYnn : 0 ≤ frobeniusNormSq Y := by
    rw [hY]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  unfold frobeniusNorm
  rw [← Real.sqrt_mul hXnn]
  -- |matrixInner X Y| = sqrt ((matrixInner X Y)^2) ≤ sqrt (frobNormSq X * frobNormSq Y)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

/-! ### T1: off-diagonal kernel magnitude -/

theorem offdiag_kernel_mag {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    |tangentCoordinateKernel S i j a b| ≤ Cker := by
  -- |K i j a b| = |⟨P_T e_ij, P_T e_ab⟩| ≤ ‖P_T e_ij‖ · ‖P_T e_ab‖.
  rw [tangentCoordinateKernel_eq_proj_inner]
  refine le_trans (matrixInner_le_frob _ _) ?_
  -- ‖P_T e_ij‖ = sqrt (K_diag i j), and K_diag i j ≤ Cker.
  have key : ∀ (x : Fin n1) (y : Fin n2),
      frobeniusNorm (tangentProjection S (coordinateMatrix x y)) ≤ Real.sqrt Cker := by
    intro x y
    unfold frobeniusNorm
    rw [hfrob x y]
    refine Real.sqrt_le_sqrt ?_
    have := hdiag x y
    exact le_trans (le_abs_self _) this
  calc frobeniusNorm (tangentProjection S (coordinateMatrix i j))
          * frobeniusNorm (tangentProjection S (coordinateMatrix a b))
        ≤ Real.sqrt Cker * Real.sqrt Cker := by
          apply mul_le_mul (key i j) (key a b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Cker := Real.mul_self_sqrt hCker

/-! ### T2: kernel-square base entry-sup bound -/

theorem base_entrysup {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤ Cker ^ 2 := by
  have hCker2 : (0 : ℝ) ≤ Cker ^ 2 := sq_nonneg _
  -- Each entry has |·| ≤ Cker^2.
  have hentry : ∀ (i : Fin n1) (j : Fin n2),
      |quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j| ≤ Cker ^ 2 := by
    intro i j
    unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
    by_cases h : (i, j) = w1
    · simp [h, hCker2]
    · rw [if_neg h, abs_mul, sq]
      exact mul_le_mul
        (offdiag_kernel_mag S Cker hdiag hCker hfrob w1.1 w1.2 i j)
        (offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2)
        (abs_nonneg _) hCker
  -- Bound the double iSup.
  unfold entrySupNorm
  refine Real.iSup_le (fun i => ?_) hCker2
  refine Real.iSup_le (fun j => ?_) hCker2
  exact hentry i j

/-! ### T3: kernel-square base Frobenius bound -/

theorem base_frob {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Real.sqrt (Cker ^ 3) := by
  -- ‖base‖²_F ≤ Cker^3, then take sqrt.
  have hsq : frobeniusNormSq (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Cker ^ 3 := by
    unfold frobeniusNormSq
    -- entry^2 ≤ Cker^2 * K(w1, ij)^2, pointwise.
    have hpt : ∀ (i : Fin n1) (j : Fin n2),
        (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2
          ≤ Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
      intro i j
      unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
      by_cases h : (i, j) = w1
      · rw [if_pos h, zero_pow (by norm_num)]
        positivity
      · rw [if_neg h, mul_pow]
        -- K(w1,ij)^2 * K(ij,w1)^2 ≤ Cker^2 * K(w1,ij)^2
        have hKle : (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2 ≤ Cker ^ 2 := by
          have := offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2
          rw [← sq_abs (tangentCoordinateKernel S i j w1.1 w1.2)]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        rw [mul_comm (tangentCoordinateKernel S w1.1 w1.2 i j ^ 2)]
        exact mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
    -- Sum the pointwise bound.
    calc (∑ i, ∑ j, (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2)
          ≤ ∑ i, ∑ j, Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact hpt i j
      _ = Cker ^ 2 * ∑ i, ∑ j, (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
      _ = Cker ^ 2 * frobeniusNormSq (tangentProjection S (coordinateMatrix w1.1 w1.2)) := by
            congr 1
            unfold frobeniusNormSq
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            -- K(w1, ij) = (P_T e_w1) i j
            rw [tangentCoordinateKernel_eq_entry]
      _ = Cker ^ 2 * tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2 := by
            rw [hfrob w1.1 w1.2]
      _ ≤ Cker ^ 2 * Cker := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact le_trans (le_abs_self _) (hdiag w1.1 w1.2)
      _ = Cker ^ 3 := by ring
  -- frobeniusNorm = sqrt frobeniusNormSq ≤ sqrt (Cker^3).
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt hsq



end MatrixCompletion

open MatrixCompletion

/-- Off-diagonal tangent-kernel magnitude bound (CR2009 §6 eq (6.1)+(6.2)),
generalizing the diagonal eq (4.8) brick to ALL index pairs via Cauchy–Schwarz. -/
theorem tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cker, hCkerpos, hbrick⟩ :=
    tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  refine ⟨Cker, hCkerpos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j a b
  set D : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hD
  have hμ₀pos : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hmin_pos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hDnn : 0 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ Cker * μ₀ := mul_nonneg (le_of_lt hCkerpos) (le_of_lt hμ₀pos)
    apply mul_nonneg h1
    apply div_nonneg (Nat.cast_nonneg r)
    exact Nat.cast_nonneg _
  have hdiag : ∀ (x : Fin n₁) (y : Fin n₂),
      |tangentCoordinateKernel S x y x y| ≤ D := by
    intro x y
    rw [hD]
    exact hbrick n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 x y
  have hfrob : ∀ (x : Fin n₁) (y : Fin n₂),
      frobeniusNormSq (tangentProjection S (coordinateMatrix x y))
        = tangentCoordinateKernel S x y x y := by
    intro x y
    rw [tangentCoordinateKernel_eq_proj_inner S x y x y]
    unfold frobeniusNormSq matrixInner
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [sq]
  exact offdiag_kernel_mag S D hdiag hDnn hfrob i j a b
end NeumannDependency17
export NeumannDependency17 (tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim)

-- Accepted proof by Minghui; submission 3f42615f-3b04-4084-a002-60e276b19f5d.
-- Original source SHA-256: 28773af36f94e530e79821b6f3fbaa7f4fa621117237f9f33414d53607a65dff.
namespace NeumannDependency18
open MatrixCompletion
open scoped Classical BigOperators

namespace ProveLinearOffdiagBaseEntryMin

theorem entry_le_sup {n₁ n₂ : Nat} (X : RealMatrix n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n₂, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

end ProveLinearOffdiagBaseEntryMin

open ProveLinearOffdiagBaseEntryMin

theorem linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cker, hCker, hker⟩ := tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
  have hsign_sup :
      entrySupNorm (signMatrix S) ≤
        μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hsign_rhs_nonneg :
      0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    positivity
  have hker_rhs_nonneg :
      0 ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
    positivity
  haveI : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  haveI : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  by_cases hdiag : (i, j) = w
  · simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag]
    positivity
  · have hsign_entry :
        |signMatrix S i j| ≤
          μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
      le_trans (entry_le_sup (signMatrix S) i j) hsign_sup
    have hker_entry :
        |tangentCoordinateKernel S i j w.1 w.2| ≤
          Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) :=
      hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j w.1 w.2
    have hprod :
        |signMatrix S i j| * |tangentCoordinateKernel S i j w.1 w.2| ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) :=
      mul_le_mul hsign_entry hker_entry (abs_nonneg _) hsign_rhs_nonneg
    calc
      |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j|
          = |signMatrix S i j| * |tangentCoordinateKernel S i j w.1 w.2| := by
            simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag, abs_mul]
      _ ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := hprod
      _ =
          Cker * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
            ring
end NeumannDependency18
export NeumannDependency18 (linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim)

-- Accepted proof by Minghui; submission c98620dd-eae0-4234-8127-c84f139b49a3.
-- Original source SHA-256: 53e4f5e0ba05e55c64305ba0a0dbfaec1f4cef17c1f44d01a182cdc28fa6ad33.
namespace NeumannDependency19
open MatrixCompletion
open scoped Classical BigOperators

namespace ProveAllDistinctInnerBaseZeroing

private theorem quadraticAllDistinctInnerBase_pointwise_abs_le_linear
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    ∀ i j,
      |quadraticAllDistinctInnerBaseMatrix S w1 w2 i j| ≤
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j| := by
  intro i j
  unfold quadraticAllDistinctInnerBaseMatrix
  unfold linearNeumannOffDiagonalCoefficientBaseMatrix
  by_cases h2 : (i, j) = w2
  · simp [h2]
  · by_cases h1 : (i, j) = w1
    · simp [h1]
    · simp [h1, h2]

private theorem quadraticAllDistinctInnerBase_frobeniusSq_le_linear
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    frobeniusNormSq (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
      frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) := by
  unfold frobeniusNormSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold quadraticAllDistinctInnerBaseMatrix
  unfold linearNeumannOffDiagonalCoefficientBaseMatrix
  by_cases h2 : (i, j) = w2
  · simp [h2]
  · by_cases h1 : (i, j) = w1
    · have h12 : w1 ≠ w2 := by
        intro h
        exact h2 (by simp [h1, h])
      simp [h1, h12, sq_nonneg]
    · simp [h1, h2]

end ProveAllDistinctInnerBaseZeroing

open ProveAllDistinctInnerBaseZeroing

theorem quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        entrySupNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) ∧
      frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) := by
  constructor
  · unfold entrySupNorm
    apply ciSup_mono
    · exact Finite.bddAbove_range
        (fun i : Fin n₁ => ⨆ j : Fin n₂,
          |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j|)
    intro i
    apply ciSup_mono
    · exact Finite.bddAbove_range
        (fun j : Fin n₂ => |linearNeumannOffDiagonalCoefficientBaseMatrix S w2 i j|)
    intro j
    exact quadraticAllDistinctInnerBase_pointwise_abs_le_linear S w1 w2 i j
  · unfold frobeniusNorm
    exact Real.sqrt_le_sqrt
      (quadraticAllDistinctInnerBase_frobeniusSq_le_linear S w1 w2)
end NeumannDependency19
export NeumannDependency19 (quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base)

-- Accepted proof by Minghui; submission aa944e5d-9892-47f4-b15d-6a912debcedd.
-- Original source SHA-256: edd42a3ab7f1219e7c1c392a556c0da680c3eca3914b86e8e7756ffc74b5b5a7.
namespace NeumannDependency20
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Centry, hCentry, hlinear⟩ :=
    linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
  refine ⟨Centry, hCentry, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  exact le_trans
    (quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base S w1 w2).1
    (hlinear n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w2)
end NeumannDependency20
export NeumannDependency20 (quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim)

-- Accepted proof by Shuze Chen; submission fcf6b81e-d8d0-4323-9581-21356ca9b948.
-- Original source SHA-256: 04d77deb4c772a48de00a5cef91c1e9ad5eaa034e0aa88820eef1cf4de6fc65d.
namespace NeumannDependency21
open MatrixCompletion

open scoped Classical BigOperators

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma coordinate_projection_kernel_norm_square
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0)
    (i : Fin N) :
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2 =
      ∑ k : Fin r, (u k i) ^ 2 := by
  calc
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2
        = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (u k a * u l a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [horth k l]
    _ = ∑ k : Fin r, (u k i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma leftSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) a b =
      if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0 := by
  unfold leftSingularProjection coordinateMatrix
  by_cases hbj : b = j
  · subst hbj
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _hx hx
      simp [hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · have hzero :
        (∀ x : Fin n₁,
          (if x = i ∧ b = j then (1 : ℝ) else 0) = 0) := by
        intro x
        simp [hbj]
    simp [hbj]

private lemma rightSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) a b =
      if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
  unfold rightSingularProjection coordinateMatrix
  by_cases hai : a = i
  · subst hai
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · have hzero :
        (∀ x : Fin n₂,
          (if a = i ∧ x = j then (1 : ℝ) else 0) = 0) := by
        intro x
        simp [hai]
    simp [hai]

private lemma twoSidedSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) a b =
      (∑ k : Fin r, S.u k a * S.u k i) *
        (∑ k : Fin r, S.v k j * S.v k b) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Finset.mul_sum, Finset.sum_mul]
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro x _hx hx
    simp [hx]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma tangentProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix i j) a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  simp [tangentProjection, leftSingularProjection_coordinate_apply,
    rightSingularProjection_coordinate_apply,
    twoSidedSingularProjection_coordinate_apply]

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection_coordinate_apply, pow_two]

private lemma coordinate_projection_square_sum
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : α → ℝ) (Q : β → ℝ) (i : α) (j : β)
    (hPi : P i = ∑ a : α, P a ^ 2)
    (hQj : Q j = ∑ b : β, Q b ^ 2) :
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2 =
      (∑ a : α, P a ^ 2) +
        (∑ b : β, Q b ^ 2) -
          (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
  classical
  let A : ℝ := ∑ a : α, P a ^ 2
  let B : ℝ := ∑ b : β, Q b ^ 2
  have hPi' : P i = A := by simpa [A] using hPi
  have hQj' : Q j = B := by simpa [B] using hQj
  have hPQ : (∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2) = A * B := by
    dsimp [A, B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hPQsq : (∑ a : α, ∑ b : β, (P a * Q b) ^ 2) = A * B := by
    calc
      ∑ a : α, ∑ b : β, (P a * Q b) ^ 2
          = ∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = A * B := hPQ
  have hCrossP : (∑ a : α, 2 * P a * (P a * B)) = 2 * A * B := by
    calc
      ∑ a : α, 2 * P a * (P a * B)
          = ∑ a : α, (2 * B) * P a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
      _ = (2 * B) * (∑ a : α, P a ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [A, mul_assoc, mul_left_comm, mul_comm]
  have hCrossQ : (∑ b : β, 2 * Q b * (A * Q b)) = 2 * A * B := by
    calc
      ∑ b : β, 2 * Q b * (A * Q b)
          = ∑ b : β, (2 * A) * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = (2 * A) * (∑ b : β, Q b ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [B, mul_assoc]
  calc
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2
        = ∑ a : α, ∑ b : β,
            ((if b = j then P a else 0) ^ 2 +
              (if a = i then Q b else 0) ^ 2 +
              (P a * Q b) ^ 2 +
              2 * (if b = j then P a else 0) *
                (if a = i then Q b else 0) -
              2 * (if b = j then P a else 0) * (P a * Q b) -
              2 * (if a = i then Q b else 0) * (P a * Q b)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
    _ = A + B + A * B + 2 * A * B - 2 * A * B - 2 * A * B := by
            simp [hPi', hQj', Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            rw [hPQsq, hCrossP, hCrossQ]
            ring
    _ = A + B - A * B := by ring
    _ = (∑ a : α, P a ^ 2) +
          (∑ b : β, Q b ^ 2) -
            (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
            simp [A, B]

private lemma tangent_projection_coordinate_frobenius_sq_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    frobeniusNormSq (tangentProjection S (coordinateMatrix i j)) =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  let P : Fin n₁ → ℝ := fun a => ∑ k : Fin r, S.u k a * S.u k i
  let Q : Fin n₂ → ℝ := fun b => ∑ k : Fin r, S.v k j * S.v k b
  have hPnorm : ∑ a : Fin n₁, P a ^ 2 = ∑ k : Fin r, (S.u k i) ^ 2 := by
    simpa [P, pow_two] using
      coordinate_projection_kernel_norm_square S.u S.u_orthonormal i
  have hQnorm : ∑ b : Fin n₂, Q b ^ 2 = ∑ k : Fin r, (S.v k j) ^ 2 := by
    have hbase :=
      coordinate_projection_kernel_norm_square S.v S.v_orthonormal j
    rw [← hbase]
    apply Finset.sum_congr rfl
    intro b _hb
    congr 1
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hPi : P i = ∑ k : Fin r, (S.u k i) ^ 2 := by
    simp [P, pow_two]
  have hQj : Q j = ∑ k : Fin r, (S.v k j) ^ 2 := by
    simp [Q, pow_two]
  unfold frobeniusNormSq
  calc
    ∑ a : Fin n₁, ∑ b : Fin n₂,
        (tangentProjection S (coordinateMatrix i j) a b) ^ 2
        = ∑ a : Fin n₁, ∑ b : Fin n₂,
            ((if b = j then P a else 0) +
              (if a = i then Q b else 0) - P a * Q b) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            rw [tangentProjection_coordinate_apply]
    _ = (∑ a : Fin n₁, P a ^ 2) +
          (∑ b : Fin n₂, Q b ^ 2) -
            (∑ a : Fin n₁, P a ^ 2) * (∑ b : Fin n₂, Q b ^ 2) := by
            exact coordinate_projection_square_sum P Q i j
              (hPi.trans hPnorm.symm) (hQj.trans hQnorm.symm)
    _ = (∑ k : Fin r, (S.u k i) ^ 2) +
          (∑ k : Fin r, (S.v k j) ^ 2) -
            (∑ k : Fin r, (S.u k i) ^ 2) *
              (∑ k : Fin r, (S.v k j) ^ 2) := by
            rw [hPnorm, hQnorm]

theorem tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNormSq (tangentProjection S (coordinateMatrix i j)) =
        tangentCoordinateKernel S i j i j := by
  intro i j
  rw [tangent_projection_coordinate_frobenius_sq_formula,
    tangent_coordinate_kernel_diagonal_formula]
end NeumannDependency21
export NeumannDependency21 (tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal)

-- Accepted proof by Shuze Chen; submission a75d3ceb-5540-469c-b958-1ca6c143f0c1.
-- Original source SHA-256: c3d1b791c15a1444d051135f4aed718039f4bbb3d54cd5eb6fb7a8e9bb8b7758.
namespace NeumannDependency22
open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5), and
PDF p. 18, equation (4.8).  Equation (3.5) defines `P_T` as the orthogonal
tangent-space projection.  Equation (4.8) uses the coordinate radius
`||P_T(e_i e_j^T)||_F`; the diagonal kernel is
`<P_T(e_i e_j^T), e_i e_j^T>`.

Reduction: the child theorem proves the substantive orthogonal-projection
identity
`||P_T(e_i e_j^T)||_F^2 = <P_T(e_i e_j^T), e_i e_j^T>`, expressed in Lean as
`frobeniusNormSq = tangentCoordinateKernel`.  The present sketch only unfolds
`frobeniusNorm = sqrt(frobeniusNormSq)` and uses `x <= |x|`.
-/

theorem tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤
        |tangentCoordinateKernel S i j i j| := by
  intro i j
  let X : Matrix (Fin n₁) (Fin n₂) ℝ :=
    tangentProjection S (coordinateMatrix i j)
  have hnormsq_nonneg : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have hnorm :
      frobeniusNorm X ^ 2 = frobeniusNormSq X := by
    simp [frobeniusNorm, Real.sq_sqrt hnormsq_nonneg]
  calc
    frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2
        = frobeniusNormSq
            (tangentProjection S (coordinateMatrix i j)) := by
          simpa [X] using hnorm
    _ = tangentCoordinateKernel S i j i j :=
        tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal S i j
    _ ≤ |tangentCoordinateKernel S i j i j| := le_abs_self _
end NeumannDependency22
export NeumannDependency22 (tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel)

-- Accepted proof by Shuze Chen; submission 4c9669b4-bdf0-44fd-8c3e-ce03721e2aa7.
-- Original source SHA-256: eb15efb5ef9a86d577a575385df44437ab3300fbccba30370391a47803f75b8c.
namespace NeumannDependency23
open MatrixCompletion

/--
Source: Candes-Recht 2008, PDF p. 18 equation (4.8), PDF p. 23 estimate
(6.2), and the rectangular-scale convention after PDF p. 24 equations
(6.2)--(6.4).

The reduction turns the A0 diagonal-kernel estimate into the Frobenius
coordinate-radius estimate used by Rudelson's selection theorem.  The geometric
child identifies the squared Frobenius norm of `P_T(e_i e_j^T)` with the
corresponding diagonal tangent kernel up to absolute value; the already-proved
A0 child bounds that kernel by `O(μ₀ r / min(n₁,n₂))`.
-/
theorem tangent_coordinate_frobenius_bound_from_a0_min_dim :
    ∃ Ccoord : ℝ, 0 < Ccoord ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        TangentCoordinateFrobeniusBound S
          (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim with
    ⟨Cker, hCker, hKernel⟩
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  have hFrob :=
    tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel S i j
  have hKer :=
    hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  refine le_trans hFrob (le_of_le_of_eq hKer ?_)
  ring
end NeumannDependency23
export NeumannDependency23 (tangent_coordinate_frobenius_bound_from_a0_min_dim)

-- Accepted proof by tianyipeng; submission 0c3960d0-51cc-49d0-bd4b-a7296fd11888.
-- Original source SHA-256: cd64861da12985650313fbd61470dfde22a64629a3a7fd5e3a01bb4293f3f64f.
namespace NeumannDependency24
open MatrixCompletion
open scoped Classical BigOperators

theorem tangent_coordinate_frobenius_sq_bound_implies_radius_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (radiusSq : ℝ) :
    0 ≤ radiusSq →
    TangentCoordinateFrobeniusBound S radiusSq →
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤
        Real.sqrt radiusSq := by
  intro _ hbound i j
  have ht : 0 ≤ frobeniusNorm (tangentProjection S (coordinateMatrix i j)) := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hb : frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤ radiusSq :=
    hbound i j
  calc frobeniusNorm (tangentProjection S (coordinateMatrix i j))
      = Real.sqrt (frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2) :=
        (Real.sqrt_sq ht).symm
    _ ≤ Real.sqrt radiusSq := Real.sqrt_le_sqrt hb
end NeumannDependency24
export NeumannDependency24 (tangent_coordinate_frobenius_sq_bound_implies_radius_bound)

-- Accepted proof by Hartmann_Psi; submission 0da34e2b-5e6d-4c62-b630-be3f80165119.
-- Original source SHA-256: 758389f90f3ad6e21e842ef300abf827e75f619b47862fa97537bbd552e9bcc0.
namespace NeumannDependency25
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem tangent_projection_self_adjoint
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (tangentProjection S A) B
      = matrixInner A (tangentProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  -- assemble
  unfold tangentProjection
  rw [matrixInner_sub_left, matrixInner_add_left, left_sa, right_sa, ts_sa,
      matrixInner_sub_right, matrixInner_add_right]
end NeumannDependency25
export NeumannDependency25 (tangent_projection_self_adjoint)

-- Accepted proof by Minghui; submission 6388eaad-7513-4c61-8e82-363b47b27991.
-- Original source SHA-256: f5c178660070f402f1933d474b28cc32271366f7b8279e409e8721a620c074da.
namespace NeumannDependency26
open MatrixCompletion
open scoped Classical BigOperators

namespace ProveTangentKernelSymm

theorem matrix_inner_coordinate
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

theorem coordinate_matrix_inner
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner (coordinateMatrix a b) X = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

end ProveTangentKernelSymm

open ProveTangentKernelSymm

theorem tangent_coordinate_kernel_symm
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i a : Fin n₁) (j b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      tangentCoordinateKernel S a b i j := by
  rw [tangentCoordinateKernel, tangentCoordinateKernel]
  rw [tangent_projection_self_adjoint]
  rw [coordinate_matrix_inner, matrix_inner_coordinate]
end NeumannDependency26
export NeumannDependency26 (tangent_coordinate_kernel_symm)

-- Accepted proof by Minghui; submission 0ac06041-6e59-4fb0-bbc1-fce0f92f058a.
-- Original source SHA-256: ebe4f99a19c1d25fddd51e3f3561ba4cc29dd5935ee33fc6f323ab7908289afd.
namespace NeumannDependency27
open MatrixCompletion
open scoped Classical BigOperators

namespace ProveLinearOffdiagBaseFrobeniusMin

theorem entry_le_sup {n₁ n₂ : Nat} (X : RealMatrix n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n₂, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

theorem matrix_inner_coordinate
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

theorem frobeniusNorm_le_mul_of_entrywise_abs_le
    {n₁ n₂ : Nat} (X Y : RealMatrix n₁ n₂) (c : ℝ)
    (hc : 0 ≤ c)
    (hentry : ∀ i j, |X i j| ≤ c * |Y i j|) :
    frobeniusNorm X ≤ c * frobeniusNorm Y := by
  have hsq_entry : ∀ i j, X i j ^ 2 ≤ c ^ 2 * Y i j ^ 2 := by
    intro i j
    have hnonneg : 0 ≤ c * |Y i j| := mul_nonneg hc (abs_nonneg _)
    have habs : |X i j| ≤ |c * (|Y i j|)| := by
      simpa [abs_of_nonneg hnonneg] using hentry i j
    have hsq := sq_le_sq.mpr habs
    calc
      X i j ^ 2 ≤ (c * |Y i j|) ^ 2 := hsq
      _ = c ^ 2 * Y i j ^ 2 := by
        rw [mul_pow, sq_abs]
  have hsum : frobeniusNormSq X ≤ c ^ 2 * frobeniusNormSq Y := by
    unfold frobeniusNormSq
    calc
      (∑ i : Fin n₁, ∑ j : Fin n₂, X i j ^ 2)
          ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, c ^ 2 * Y i j ^ 2 := by
            exact Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ => hsq_entry i j))
      _ = c ^ 2 * (∑ i : Fin n₁, ∑ j : Fin n₂, Y i j ^ 2) := by
            simp [Finset.mul_sum]
  calc
    frobeniusNorm X = Real.sqrt (frobeniusNormSq X) := rfl
    _ ≤ Real.sqrt (c ^ 2 * frobeniusNormSq Y) := Real.sqrt_le_sqrt hsum
    _ = c * frobeniusNorm Y := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
      rfl

end ProveLinearOffdiagBaseFrobeniusMin

open ProveLinearOffdiagBaseFrobeniusMin

theorem linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Ccoord, hCcoord, hcoord⟩ := tangent_coordinate_frobenius_bound_from_a0_min_dim
  refine ⟨Real.sqrt Ccoord, Real.sqrt_pos.2 hCcoord, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
  have hsign_sup :
      entrySupNorm (signMatrix S) ≤
        μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hsign_nonneg :
      0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    positivity
  let Tcoord : RealMatrix n₁ n₂ := tangentProjection S (coordinateMatrix w.1 w.2)
  have hentry :
      ∀ i j,
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j| ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * |Tcoord i j| := by
    intro i j
    by_cases hdiag : (i, j) = w
    · calc
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j| = 0 := by
          simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag]
        _ ≤
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              |Tcoord i j| := by
            exact mul_nonneg hsign_nonneg (abs_nonneg _)
    · have hsign_entry :
          |signMatrix S i j| ≤
            μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
        le_trans (entry_le_sup (signMatrix S) i j) hsign_sup
      have hkernel_eq :
          tangentCoordinateKernel S i j w.1 w.2 = Tcoord i j := by
        rw [tangent_coordinate_kernel_symm]
        rw [tangentCoordinateKernel, matrix_inner_coordinate]
      calc
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j|
            = |signMatrix S i j| * |Tcoord i j| := by
              simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag, abs_mul, hkernel_eq]
        _ ≤
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              |Tcoord i j| := by
              exact mul_le_mul_of_nonneg_right hsign_entry (abs_nonneg _)
  have hbase_le :
      frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          frobeniusNorm Tcoord :=
    frobeniusNorm_le_mul_of_entrywise_abs_le
      (linearNeumannOffDiagonalCoefficientBaseMatrix S w) Tcoord
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) hsign_nonneg hentry
  have hradiusSq_nonneg :
      0 ≤ Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
    positivity
  have hcoord_bound :
      TangentCoordinateFrobeniusBound S
        (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) :=
    hcoord n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hTcoord_le :
      frobeniusNorm Tcoord ≤
        Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    exact tangent_coordinate_frobenius_sq_bound_implies_radius_bound
      S (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
      hradiusSq_nonneg hcoord_bound w.1 w.2
  have hmul :
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          frobeniusNorm Tcoord ≤
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    exact mul_le_mul_of_nonneg_left hTcoord_le hsign_nonneg
  have hsqrt_split :
      Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) =
        Real.sqrt Ccoord *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    have hrest : 0 ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
      positivity
    have hrewrite :
        Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) =
          Ccoord * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
      ring
    rw [hrewrite, Real.sqrt_mul (le_of_lt hCcoord)]
  calc
    frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
        ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            frobeniusNorm Tcoord := hbase_le
    _ ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := hmul
    _ =
          Real.sqrt Ccoord * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
        rw [hsqrt_split]
        ring
end NeumannDependency27
export NeumannDependency27 (linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim)

-- Accepted proof by Minghui; submission 944346c7-3381-4642-aa84-b43b161cb434.
-- Original source SHA-256: 13b447d0ed8090c2f8951eca82a1a1de77ee28f4f2f90a3b3b1aff505ac98156.
namespace NeumannDependency28
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cfro, hCfro, hlinear⟩ :=
    linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
  refine ⟨Cfro, hCfro, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  exact le_trans
    (quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base S w1 w2).2
    (hlinear n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w2)
end NeumannDependency28
export NeumannDependency28 (quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim)

-- Accepted proof by Minghui; submission bee55c0b-5823-4f86-96f1-cdfa92a76690.
-- Original source SHA-256: 7de115e77beb7073bece1dfeec86fdb7ae5d375da0e3a898301b3bfc4077edc2.
namespace NeumannDependency29
open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletionA0DefaultA1

private theorem coordinate_sq_sum_le_of_coherence
    {N r : Nat} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r -> Fin N -> ℝ) (μ : ℝ)
    (hcoh : coherence N r u <= μ) (i : Fin N) :
    (∑ k : Fin r, (u k i) ^ 2) <= μ * (r : ℝ) / (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  let U : ℝ := ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2
  have hi_le : (∑ k : Fin r, (u k i) ^ 2) <= U := by
    exact le_ciSup (Finite.bddAbove_range fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hfactor_pos : 0 < (N : ℝ) / (r : ℝ) := div_pos hNreal hrreal
  have hmul : ((N : ℝ) / (r : ℝ)) * U <= μ := by
    simpa [coherence, U] using hcoh
  have hU_le_div : U <= μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hfactor_pos]
    simpa [mul_comm] using hmul
  have hdiv : μ / ((N : ℝ) / (r : ℝ)) = μ * (r : ℝ) / (N : ℝ) := by
    field_simp [ne_of_gt hNreal, ne_of_gt hrreal]
  exact hi_le.trans (by simpa [hdiv] using hU_le_div)

private theorem sqrt_default_product
    {n₁ n₂ r : Nat} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    {μ₀ : ℝ} (hμ₀ : 0 <= μ₀) :
    Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) =
      μ₀ * Real.sqrt (r : ℝ) *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  have hn₁real : 0 < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂real : 0 < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hleft_nonneg : 0 <= μ₀ * (r : ℝ) / (n₁ : ℝ) := by positivity
  calc
    Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))
        = Real.sqrt
            ((μ₀ * (r : ℝ) / (n₁ : ℝ)) * (μ₀ * (r : ℝ) / (n₂ : ℝ))) := by
            rw [Real.sqrt_mul hleft_nonneg]
    _ = Real.sqrt
            (μ₀ ^ 2 * ((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            congr 1
            field_simp [ne_of_gt hn₁real, ne_of_gt hn₂real]
    _ = Real.sqrt (μ₀ ^ 2) *
            Real.sqrt (((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            rw [Real.sqrt_mul (sq_nonneg μ₀)]
    _ = μ₀ * Real.sqrt (((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ))) ) := by
            rw [Real.sqrt_sq hμ₀]
    _ = μ₀ *
          Real.sqrt ((r : ℝ) * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            congr 1
            congr 1
            field_simp [ne_of_gt hn₁real, ne_of_gt hn₂real]
    _ = μ₀ * (Real.sqrt (r : ℝ) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            rw [Real.sqrt_mul (le_of_lt hrreal)]
    _ = μ₀ * Real.sqrt (r : ℝ) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
            ring

private theorem a0_to_default_a1
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (μ₀ : ℝ) (S : SVD M r) :
    0 < n₁ -> 0 < n₂ -> 0 < r ->
    0 <= μ₀ -> A0 S μ₀ -> A1 S (defaultA1Parameter μ₀ r) := by
  intro hn₁ hn₂ hr hμ₀ hA0 i j
  have hsumu_nonneg : 0 <= ∑ k : Fin r, (S.u k i) ^ 2 := by
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hsumv_nonneg : 0 <= ∑ k : Fin r, (S.v k j) ^ 2 := by
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hsumu_le :
      (∑ k : Fin r, (S.u k i) ^ 2) <= μ₀ * (r : ℝ) / (n₁ : ℝ) :=
    coordinate_sq_sum_le_of_coherence hn₁ hr S.u μ₀ hA0.1 i
  have hsumv_le :
      (∑ k : Fin r, (S.v k j) ^ 2) <= μ₀ * (r : ℝ) / (n₂ : ℝ) :=
    coordinate_sq_sum_le_of_coherence hn₂ hr S.v μ₀ hA0.2 j
  have hsumu_bound_nonneg : 0 <= μ₀ * (r : ℝ) / (n₁ : ℝ) := by
    positivity
  have hcsq :
      (∑ k : Fin r, S.u k i * S.v k j) ^ 2 <=
        (∑ k : Fin r, (S.u k i) ^ 2) * (∑ k : Fin r, (S.v k j) ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r))
        (fun k : Fin r => S.u k i) (fun k : Fin r => S.v k j))
  have habs_le :
      |∑ k : Fin r, S.u k i * S.v k j| <=
        Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) :=
    Real.abs_le_sqrt hcsq
  have hsqrt_le :
      Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) <=
        Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
    have hprod_le :
        (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) <=
          (μ₀ * (r : ℝ) / (n₁ : ℝ)) * (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      exact mul_le_mul hsumu_le hsumv_le hsumv_nonneg hsumu_bound_nonneg
    calc
      Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2))
          <= Real.sqrt ((μ₀ * (r : ℝ) / (n₁ : ℝ)) *
              (μ₀ * (r : ℝ) / (n₂ : ℝ))) := Real.sqrt_le_sqrt hprod_le
      _ = Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
            rw [Real.sqrt_mul]
            positivity
  have hsign_eq :
      signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
    rw [signMatrix]
    simpa [Matrix.vecMulVec_apply] using
      (Matrix.sum_apply i j (Finset.univ : Finset (Fin r))
        (fun k : Fin r => Matrix.vecMulVec (S.u k) (S.v k)))
  calc
    |signMatrix S i j|
        = |∑ k : Fin r, S.u k i * S.v k j| := by rw [hsign_eq]
    _ <= Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) := habs_le
    _ <= Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := hsqrt_le
    _ = defaultA1Parameter μ₀ r *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
            rw [defaultA1Parameter, sqrt_default_product hn₁ hn₂ hr hμ₀]

end MatrixCompletionA0DefaultA1

theorem a0_implies_default_a1_parameter :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ -> 0 < n₂ -> 0 < r ->
      0 <= μ₀ -> A0 S μ₀ -> A1 S (defaultA1Parameter μ₀ r) := by
  intro n₁ n₂ r M μ₀ S
  exact MatrixCompletionA0DefaultA1.a0_to_default_a1 μ₀ S
end NeumannDependency29
export NeumannDependency29 (a0_implies_default_a1_parameter)

-- Accepted proof by tianyipeng; submission d7bd8a03-9be5-4835-9a0e-ee16b9b6bce4.
-- Original source SHA-256: cd2da6cb8246b7f004c30f404dbe6623be7ccd30d7d5237e3fd312c019c28001.
namespace NeumannDependency30
open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_event_probability_mono
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, EventA Omega → EventB Omega) →
    bernoulliEventProb p EventA ≤ bernoulliEventProb p EventB := by
  intro hp0 hp1 hAB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : EventA Omega
  · rw [if_pos hA, if_pos (hAB Omega hA)]
  · rw [if_neg hA]
    by_cases hB : EventB Omega
    · rw [if_pos hB]; exact hw Omega
    · rw [if_neg hB]
end NeumannDependency30
export NeumannDependency30 (bernoulli_event_probability_mono)

end NeumannProof


set_option autoImplicit false

namespace NeumannScalar

lemma density_polynomial_bounds (t n d m B lam : ℝ)
    (ht : 1 ≤ t) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 1 ≤ B) (hlam : 1 ≤ lam)
    (hlower : lam * t ^ ((4 : ℝ) / 3) * n * B ≤ m)
    (hupper : m ≤ n * d) :
    lam * t ^ 3 * B ≤ d * m ∧
      lam ^ 2 * t ^ 4 * n * B ^ 2 ≤ d * m ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have ht4 : 0 < t ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos ht0 _
  have hfirst : t ^ ((4 : ℝ) / 3) * n ≤ m := by
    calc
      t ^ ((4 : ℝ) / 3) * n = 1 * t ^ ((4 : ℝ) / 3) * n * 1 := by ring
      _ ≤ lam * t ^ ((4 : ℝ) / 3) * n * B := by gcongr
      _ ≤ m := hlower
  have htd : t ^ ((4 : ℝ) / 3) ≤ d := by
    apply (mul_le_mul_iff_left₀ hn0).mp
    nlinarith [hfirst.trans hupper]
  have hthird : t ^ ((1 : ℝ) / 3) ≤ n :=
    (Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1 : ℝ) / 3 ≤ 4 / 3)).trans
      (htd.trans hdn)
  have hfive : t ^ ((5 : ℝ) / 3) ≤ d * n := by
    have h := mul_le_mul htd hthird (Real.rpow_nonneg ht0.le _) hd0.le
    rw [← Real.rpow_add ht0] at h
    norm_num at h ⊢
    exact h
  have hthree : t ^ (3 : ℕ) = t ^ ((4 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hfour : t ^ (4 : ℕ) = (t ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (t ^ ((4 : ℝ) / 3)) 3, ← Real.rpow_mul ht0.le]
    norm_num
  constructor
  · calc
      lam * t ^ 3 * B = lam * t ^ ((4 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) * B := by
        rw [hthree]; ring
      _ ≤ lam * t ^ ((4 : ℝ) / 3) * (d * n) * B := by gcongr
      _ = d * (lam * t ^ ((4 : ℝ) / 3) * n * B) := by ring
      _ ≤ d * m := mul_le_mul_of_nonneg_left hlower hd0.le
  · have htdn : t ^ ((4 : ℝ) / 3) ≤ d * n := by nlinarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ lam * t ^ ((4 : ℝ) / 3) * n * B) hlower 2
    calc
      lam ^ 2 * t ^ 4 * n * B ^ 2 =
          (lam ^ 2 * (t ^ ((4 : ℝ) / 3)) ^ 2 * n * B ^ 2) * t ^ ((4 : ℝ) / 3) := by
        rw [hfour]; ring
      _ ≤ (lam ^ 2 * (t ^ ((4 : ℝ) / 3)) ^ 2 * n * B ^ 2) * (d * n) := by gcongr
      _ = d * (lam * t ^ ((4 : ℝ) / 3) * n * B) ^ 2 := by ring
      _ ≤ d * m ^ 2 := mul_le_mul_of_nonneg_left hsq hd0.le

theorem density_scale_bounds (t n d m B lam : ℝ)
    (ht : 1 ≤ t) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 1 ≤ B) (hlam : 1 ≤ lam)
    (hlower : lam * t ^ ((4 : ℝ) / 3) * n * B ≤ m)
    (hupper : m ≤ n * d) :
    t * Real.sqrt (t / d) * Real.sqrt (B / m) ≤ lam ^ (-((1 : ℝ) / 2)) ∧
      B / m * t ^ 2 * Real.sqrt (n / d) ≤ lam ^ (-((1 : ℝ) / 2)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hlower
  have hroot : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hpower : lam ^ (-((1 : ℝ) / 2)) = 1 / Real.sqrt lam := by
    rw [Real.rpow_neg hlam0.le, ← Real.sqrt_eq_rpow, one_div]
  obtain ⟨hfirst, hsecond⟩ := density_polynomial_bounds t n d m B lam
    ht hn hd hdn hB hlam hlower hupper
  have hfrel : (t * Real.sqrt (t / d) * Real.sqrt (B / m)) ^ 2 * (d * m) = t ^ 3 * B := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg ht0.le hd0.le),
      Real.sq_sqrt (div_nonneg hB0.le hm0.le)]
    field_simp
    <;> ring
  have herel : (B / m * t ^ 2 * Real.sqrt (n / d)) ^ 2 * (d * m ^ 2) =
      t ^ 4 * n * B ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hn0.le hd0.le)]
    field_simp
    <;> ring
  have hf : (t * Real.sqrt (t / d) * Real.sqrt (B / m) * Real.sqrt lam) ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hd0 hm0)).mp
    calc
      (d * m) * (t * Real.sqrt (t / d) * Real.sqrt (B / m) * Real.sqrt lam) ^ 2 =
          lam * ((t * Real.sqrt (t / d) * Real.sqrt (B / m)) ^ 2 * (d * m)) := by
        rw [mul_pow, Real.sq_sqrt hlam0.le]; ring
      _ = lam * (t ^ 3 * B) := by rw [hfrel]
      _ ≤ (d * m) * 1 := by nlinarith [hfirst]
  have he : (B / m * t ^ 2 * Real.sqrt (n / d) * lam) ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hd0 (sq_pos_of_pos hm0))).mp
    calc
      (d * m ^ 2) * (B / m * t ^ 2 * Real.sqrt (n / d) * lam) ^ 2 =
          lam ^ 2 * ((B / m * t ^ 2 * Real.sqrt (n / d)) ^ 2 * (d * m ^ 2)) := by ring
      _ = lam ^ 2 * (t ^ 4 * n * B ^ 2) := by rw [herel]
      _ ≤ (d * m ^ 2) * 1 := by nlinarith [hsecond]
  rw [hpower]
  constructor
  · apply (le_div_iff₀ hroot).mpr
    nlinarith
  · have hsmall : B / m * t ^ 2 * Real.sqrt (n / d) ≤ 1 / lam := by
      apply (le_div_iff₀ hlam0).mpr
      nlinarith
    exact hsmall.trans (one_div_le_one_div_of_le hroot
      (Real.sqrt_le_self_iff.mpr (Or.inr hlam)))

lemma variance_scale_normalize (mu r n d m B : ℝ)
    (hmu : 0 ≤ mu) (hr : 0 ≤ r) (hn : 0 < n) (hd : 0 < d)
    (hm : 0 < m) (hB : 0 ≤ B) :
    Real.sqrt (B / (m / (n * d))) *
        (mu * Real.sqrt r * Real.sqrt (r / (n * d)) * Real.sqrt (mu * r / d)) =
      (mu * r) * Real.sqrt (mu * r / d) * Real.sqrt (B / m) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ B / (m / (n * d))), Real.sq_sqrt hr,
    Real.sq_sqrt (by positivity : 0 ≤ r / (n * d)),
    Real.sq_sqrt (by positivity : 0 ≤ mu * r / d),
    Real.sq_sqrt (by positivity : 0 ≤ B / m)]
  field_simp
  <;> ring

lemma entry_scale_normalize (mu r n d m B : ℝ)
    (hmu : 0 ≤ mu) (hr : 0 ≤ r) (hn : 0 < n) (hd : 0 < d)
    (hm : 0 < m) (hB : 0 ≤ B) :
    (B / (m / (n * d))) *
        (mu * Real.sqrt r * Real.sqrt (r / (n * d)) * (mu * r / d)) =
      B / m * (mu * r) ^ 2 * Real.sqrt (n / d) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow]
  rw [Real.sq_sqrt hr, Real.sq_sqrt (by positivity : 0 ≤ r / (n * d)),
    Real.sq_sqrt (by positivity : 0 ≤ n / d)]
  field_simp
  <;> ring

end NeumannScalar

open MatrixCompletion NeumannProof
open scoped BigOperators

theorem unshifted_structural_tail :
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Centry, hCentry, hentry⟩ :=
    quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
  obtain ⟨Cfro, hCfro, hfro⟩ :=
    quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
  obtain ⟨Cbern, cbern, hCbern, hcbern, hraw⟩ :=
    quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim
      Centry Cfro hCentry hCfro
  refine ⟨Cbern * (Cfro + Centry), cbern + 1, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ _hμ₁ hA0 _hA1
    hsample hrepr w1 w2
  let n : ℝ := (max n₁ n₂ : ℕ)
  let d : ℝ := (min n₁ n₂ : ℕ)
  let B : ℝ := β * Real.log n
  let t : ℝ := μ₀ * (r : ℝ)
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : 0 < (n₁ : ℝ) * (n₂ : ℝ))).mpr
    exact_mod_cast hm
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ max n₁ n₂ by omega)
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast (show 1 ≤ min n₁ n₂ by omega)
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hdn : d ≤ n := by
    dsimp [d, n]
    exact_mod_cast (show min n₁ n₂ ≤ max n₁ n₂ from min_le_max)
  have hprod : n * d = (n₁ : ℝ) * (n₂ : ℝ) := by
    dsimp [n, d]
    exact_mod_cast (max_mul_min n₁ n₂)
  have hprobnonneg : 0 ≤ bernoulliEventProb p
      (fun Omega3 => |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤
        Cbern * (Cfro + Centry) * lam ^ (-((1 : ℝ) / 2))) := by
    unfold bernoulliEventProb
    apply Finset.sum_nonneg
    intro Omega3 _
    split_ifs
    · unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
    · exact le_rfl
  by_cases hlarge : 2 ≤ max n₁ n₂
  · have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hlogn : (1 : ℝ) / 2 ≤ Real.log n :=
      hlogtwo.trans (Real.log_le_log (by norm_num) (by dsimp [n]; exact_mod_cast hlarge))
    have hB : 1 ≤ B := by
      dsimp [B]
      calc
        (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ β * Real.log n := mul_le_mul hβ.le hlogn (by norm_num) (by linarith)
    have ht : 1 ≤ t := by
      dsimp [t]
      exact one_le_mul_of_one_le_of_one_le hμ₀ (by exact_mod_cast (show 1 ≤ r by omega))
    have hlower : lam * t ^ ((4 : ℝ) / 3) * n * B ≤ (m : ℝ) := by
      calc
        lam * t ^ ((4 : ℝ) / 3) * n * B =
            lam * μ₀ ^ ((4 : ℝ) / 3) * (↑(max n₁ n₂)) *
              (r : ℝ) ^ ((4 : ℝ) / 3) * (β * Real.log (↑(max n₁ n₂))) := by
          dsimp [t, n, B]
          rw [Real.mul_rpow (by linarith : 0 ≤ μ₀) (Nat.cast_nonneg r)]
          ring
        _ ≤ (m : ℝ) := hsample
    have hupper : (m : ℝ) ≤ n * d := by rw [hprod]; exact_mod_cast hm
    have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hlower
    have hscales := NeumannScalar.density_scale_bounds t n d (m : ℝ) B lam
      ht hn hd hdn hB hlam hlower hupper
    have hvariance :
        Real.sqrt (B / p) *
          (defaultA1Parameter μ₀ r * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            Real.sqrt (μ₀ * (r : ℝ) / d)) ≤ lam ^ (-((1 : ℝ) / 2)) := by
      dsimp [defaultA1Parameter, p]
      rw [← hprod]
      rw [NeumannScalar.variance_scale_normalize μ₀ (r : ℝ) n d (m : ℝ) B
        (by linarith) (Nat.cast_nonneg r) hn0 hd0 hm0 (by linarith)]
      exact hscales.1
    have hentryScale :
        (B / p) *
          (defaultA1Parameter μ₀ r * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / d)) ≤ lam ^ (-((1 : ℝ) / 2)) := by
      dsimp [defaultA1Parameter, p]
      rw [← hprod]
      rw [NeumannScalar.entry_scale_normalize μ₀ (r : ℝ) n d (m : ℝ) B
        (by linarith) (Nat.cast_nonneg r) hn0 hd0 hm0 (by linarith)]
      exact hscales.2
    have hdefault : 1 ≤ defaultA1Parameter μ₀ r := by
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ r by omega))
      exact one_le_mul_of_one_le_of_one_le hμ₀ hsqrt
    have hA1default := a0_implies_default_a1_parameter n₁ n₂ r M μ₀ S
      hn₁ hn₂ hr (by linarith) hA0
    have hrawProb := hraw β hβ n₁ n₂ r m M μ₀ (defaultA1Parameter μ₀ r) S
      hn₁ hn₂ hr hm hμ₀ hdefault hA0 hA1default hrepr
      (hentry n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault hA0 hA1default)
      (hfro n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault hA0 hA1default) w1 w2
    have hfail : 1 - (cbern + 1) * n ^ (-β) ≤ 1 - cbern * n ^ (-β) := by
      nlinarith [Real.rpow_nonneg hn0.le (-β)]
    have htotal := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hvariance hCfro.le)
        (mul_le_mul_of_nonneg_left hentryScale hCentry.le)) hCbern.le
    refine hfail.trans (hrawProb.trans ?_)
    apply bernoulli_event_probability_mono p _ _ hp0 hp1
    intro Omega3 hOmega3
    apply hOmega3.trans
    convert htotal using 1 <;> dsimp [B, p, n, d] <;> ring
  · have hone : max n₁ n₂ = 1 := by omega
    have hfail : 1 - (cbern + 1) * (↑(max n₁ n₂) : ℝ) ^ (-β) ≤ 0 := by
      rw [hone]
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      linarith
    exact hfail.trans hprobnonneg

open MatrixCompletion NeumannProof

lemma shifted_bernstein_scale (C e f beta L p : ℝ)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hbeta : 2 < beta) (hL : 0 ≤ L) (hp : 0 ≤ p) :
    C * (Real.sqrt (((beta + 4) * L) / p) * f +
      (((beta + 4) * L) / p) * e) ≤
    (3 * C) * (Real.sqrt ((beta * L) / p) * f +
      ((beta * L) / p) * e) := by
  have hbase : 0 ≤ beta * L / p := div_nonneg (mul_nonneg (by linarith) hL) hp
  have hratio : (beta + 4) * L / p ≤ 3 * (beta * L / p) := by
    calc
      (beta + 4) * L / p ≤ (3 * beta) * L / p :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hL) hp
      _ = 3 * (beta * L / p) := by ring
  have hroot : Real.sqrt (((beta + 4) * L) / p) ≤
      3 * Real.sqrt ((beta * L) / p) := by
    calc
      Real.sqrt (((beta + 4) * L) / p) ≤ Real.sqrt (9 * (beta * L / p)) :=
        Real.sqrt_le_sqrt (hratio.trans (by linarith))
      _ = 3 * Real.sqrt ((beta * L) / p) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  calc
    C * (Real.sqrt (((beta + 4) * L) / p) * f +
        (((beta + 4) * L) / p) * e) ≤
        C * ((3 * Real.sqrt ((beta * L) / p)) * f +
          (3 * (beta * L / p)) * e) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hroot hf)
          (mul_le_mul_of_nonneg_right hratio he)) hC
    _ = (3 * C) * (Real.sqrt ((beta * L) / p) * f +
        ((beta * L) / p) * e) := by ring


theorem shifted_structural_tail :
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 4)) := by
  obtain ⟨Centry, hCentry, hentry⟩ :=
    quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
  obtain ⟨Cfro, hCfro, hfro⟩ :=
    quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
  obtain ⟨Cbern, cbern, hCbern, hcbern, hraw⟩ :=
    quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim
      Centry Cfro hCentry hCfro
  refine ⟨(3 * Cbern) * (Cfro + Centry), cbern + 1, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ _hμ₁ hA0 _hA1
    hsample hrepr w1 w2
  let n : ℝ := (max n₁ n₂ : ℕ)
  let d : ℝ := (min n₁ n₂ : ℕ)
  let B : ℝ := β * Real.log n
  let t : ℝ := μ₀ * (r : ℝ)
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : 0 < (n₁ : ℝ) * (n₂ : ℝ))).mpr
    exact_mod_cast hm
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ max n₁ n₂ by omega)
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast (show 1 ≤ min n₁ n₂ by omega)
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hdn : d ≤ n := by
    dsimp [d, n]
    exact_mod_cast (show min n₁ n₂ ≤ max n₁ n₂ from min_le_max)
  have hprod : n * d = (n₁ : ℝ) * (n₂ : ℝ) := by
    dsimp [n, d]
    exact_mod_cast (max_mul_min n₁ n₂)
  have hprobnonneg : 0 ≤ bernoulliEventProb p
      (fun Omega3 => |quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2| ≤
        (3 * Cbern) * (Cfro + Centry) * lam ^ (-((1 : ℝ) / 2))) := by
    unfold bernoulliEventProb
    apply Finset.sum_nonneg
    intro Omega3 _
    split_ifs
    · unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
    · exact le_rfl
  by_cases hlarge : 2 ≤ max n₁ n₂
  · have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hlogn : (1 : ℝ) / 2 ≤ Real.log n :=
      hlogtwo.trans (Real.log_le_log (by norm_num) (by dsimp [n]; exact_mod_cast hlarge))
    have hB : 1 ≤ B := by
      dsimp [B]
      calc
        (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ β * Real.log n := mul_le_mul hβ.le hlogn (by norm_num) (by linarith)
    have ht : 1 ≤ t := by
      dsimp [t]
      exact one_le_mul_of_one_le_of_one_le hμ₀ (by exact_mod_cast (show 1 ≤ r by omega))
    have hlower : lam * t ^ ((4 : ℝ) / 3) * n * B ≤ (m : ℝ) := by
      calc
        lam * t ^ ((4 : ℝ) / 3) * n * B =
            lam * μ₀ ^ ((4 : ℝ) / 3) * (↑(max n₁ n₂)) *
              (r : ℝ) ^ ((4 : ℝ) / 3) * (β * Real.log (↑(max n₁ n₂))) := by
          dsimp [t, n, B]
          rw [Real.mul_rpow (by linarith : 0 ≤ μ₀) (Nat.cast_nonneg r)]
          ring
        _ ≤ (m : ℝ) := hsample
    have hupper : (m : ℝ) ≤ n * d := by rw [hprod]; exact_mod_cast hm
    have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hlower
    have hscales := NeumannScalar.density_scale_bounds t n d (m : ℝ) B lam
      ht hn hd hdn hB hlam hlower hupper
    have hvariance :
        Real.sqrt (B / p) *
          (defaultA1Parameter μ₀ r * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            Real.sqrt (μ₀ * (r : ℝ) / d)) ≤ lam ^ (-((1 : ℝ) / 2)) := by
      dsimp [defaultA1Parameter, p]
      rw [← hprod]
      rw [NeumannScalar.variance_scale_normalize μ₀ (r : ℝ) n d (m : ℝ) B
        (by linarith) (Nat.cast_nonneg r) hn0 hd0 hm0 (by linarith)]
      exact hscales.1
    have hentryScale :
        (B / p) *
          (defaultA1Parameter μ₀ r * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / d)) ≤ lam ^ (-((1 : ℝ) / 2)) := by
      dsimp [defaultA1Parameter, p]
      rw [← hprod]
      rw [NeumannScalar.entry_scale_normalize μ₀ (r : ℝ) n d (m : ℝ) B
        (by linarith) (Nat.cast_nonneg r) hn0 hd0 hm0 (by linarith)]
      exact hscales.2
    have hdefault : 1 ≤ defaultA1Parameter μ₀ r := by
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ r by omega))
      exact one_le_mul_of_one_le_of_one_le hμ₀ hsqrt
    have hA1default := a0_implies_default_a1_parameter n₁ n₂ r M μ₀ S
      hn₁ hn₂ hr (by linarith) hA0
    have hrawProb := hraw (β + 4) (by linarith) n₁ n₂ r m M μ₀ (defaultA1Parameter μ₀ r) S
      hn₁ hn₂ hr hm hμ₀ hdefault hA0 hA1default hrepr
      (hentry n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault hA0 hA1default)
      (hfro n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault hA0 hA1default) w1 w2
    have hfail : 1 - (cbern + 1) * n ^ (-(β + 4)) ≤ 1 - cbern * n ^ (-(β + 4)) := by
      nlinarith [Real.rpow_nonneg hn0.le (-(β + 4))]
    have htotal := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hvariance hCfro.le)
        (mul_le_mul_of_nonneg_left hentryScale hCentry.le)) (show 0 ≤ 3 * Cbern by positivity)
    let e : ℝ := Centry * defaultA1Parameter μ₀ r *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (μ₀ * (r : ℝ) / d)
    let f : ℝ := Cfro * defaultA1Parameter μ₀ r *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt (μ₀ * (r : ℝ) / d)
    have he : 0 ≤ e := by dsimp [e, defaultA1Parameter]; positivity
    have hf : 0 ≤ f := by dsimp [f, defaultA1Parameter]; positivity
    have hshift := shifted_bernstein_scale Cbern e f β (Real.log n) p
      hCbern.le he hf hβ (by linarith) hp0
    have hfinal : Cbern *
        (Real.sqrt (((β + 4) * Real.log n) / p) * f +
          (((β + 4) * Real.log n) / p) * e) ≤
        (3 * Cbern) * (Cfro + Centry) * lam ^ (-((1 : ℝ) / 2)) := by
      apply hshift.trans
      convert htotal using 1 <;> (try dsimp [e, f, B, p, n, d]) <;> ring
    refine hfail.trans (hrawProb.trans ?_)
    apply bernoulli_event_probability_mono p _ _ hp0 hp1
    intro Omega3 hOmega3
    apply hOmega3.trans
    exact hfinal
  · have hone : max n₁ n₂ = 1 := by omega
    have hfail : 1 - (cbern + 1) * (↑(max n₁ n₂) : ℝ) ^ (-(β + 4)) ≤ 0 := by
      rw [hone]
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      linarith
    exact hfail.trans hprobnonneg

-- Accepted proof by tianyipeng; submission 90adc9be-985a-4a65-ac00-aab2d6cbbac1.
-- Original SHA-256: 97a6e894149d8e1177b2d2230cc1b788c12f6035af41066acaaad4b9b05752da.
namespace UniformDependency0
open MatrixCompletion
open scoped Classical BigOperators
open Finset

private theorem bern_total {n₁ n₂ : ℕ} (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  unfold bernoulliObservationWeight
  rw [← Finset.powerset_univ]
  have key := Finset.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1:ℝ) - p) Finset.univ
  have hL : ∏ _i : Fin n₁ × Fin n₂, (p + (1 - p)) = 1 := by
    rw [Finset.prod_const, Finset.card_univ]
    have h1 : p + (1 - p) = 1 := by ring
    rw [h1, one_pow]
  rw [hL] at key
  refine Eq.trans ?_ key.symm
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const, Finset.prod_const]
  rw [show (univ \ t).card = Fintype.card (Fin n₁ × Fin n₂) - t.card from by
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]]

theorem bernoulli_event_intersection_probability_from_lower_bounds
    {n₁ n₂ : ℕ} (p cA cB failureScale : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p EventA ≥ 1 - cA * failureScale →
    bernoulliEventProb p EventB ≥ 1 - cB * failureScale →
    bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≥
      1 - (cA + cB) * failureScale := by
  intro hp0 hp1 hA hB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have key : bernoulliEventProb p EventA + bernoulliEventProb p EventB
              - bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≤ 1 := by
    rw [← bern_total (n₁ := n₁) (n₂ := n₂) p]
    unfold bernoulliEventProb
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro Omega _
    have hwO := hw Omega
    by_cases hA' : EventA Omega
    · by_cases hB' : EventB Omega
      · simp only [if_pos hA', if_pos hB', if_pos (And.intro hA' hB')]; linarith
      · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hB' h.2
        simp only [if_pos hA', if_neg hB', if_neg hn]; linarith
    · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hA' h.1
      by_cases hB' : EventB Omega
      · simp only [if_neg hA', if_pos hB', if_neg hn]; linarith
      · simp only [if_neg hA', if_neg hB', if_neg hn]; linarith
  have hexp : (cA + cB) * failureScale = cA * failureScale + cB * failureScale := by ring
  linarith [key, hA, hB, hexp]
end UniformDependency0
export UniformDependency0 (bernoulli_event_intersection_probability_from_lower_bounds)

-- Accepted proof by Shuze Chen; submission d96236fe-dc5a-4196-ace2-62a6cfe0985e.
-- Original SHA-256: a2ffdfc84af425cab3f9bb6480a9237433dcae46efc63d20923ef86ace6ae426.
namespace UniformDependency1
open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma bernoulliEventProb_true
    {n₁ n₂ : ℕ} (p : ℝ) :
    bernoulliEventProb p (fun _ : Finset (Fin n₁ × Fin n₂) => True) = 1 := by
  unfold bernoulliEventProb
  simpa using (bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p))

private theorem finite_pair_intersection_aux
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event :
      ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) →
        Finset (Fin n₁ × Fin n₂) → Prop)
    (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hPoint :
      ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
        bernoulliEventProb p (Event pair) ≥ 1 - c * failureScale) :
    ∀ s : Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)),
      bernoulliEventProb p
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega) ≥
        1 - (((s.card : ℝ) * c) * failureScale) := by
  intro s
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bernoulliEventProb_true]
  | insert a s ha ih =>
      have hA :
          bernoulliEventProb p (Event a) ≥ 1 - c * failureScale :=
        hPoint a
      have hB :
          bernoulliEventProb p
              (fun Omega =>
                ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega) ≥
            1 - ((s.card : ℝ) * c) * failureScale :=
        ih
      have hInter :=
        bernoulli_event_intersection_probability_from_lower_bounds
          p c ((s.card : ℝ) * c) failureScale
          (Event a)
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega)
          hp hp_one hA hB
      have hcard : (insert a s).card = s.card + 1 := by
        simp [ha]
      have hconst :
          (c + (s.card : ℝ) * c) * failureScale =
            (((insert a s).card : ℝ) * c) * failureScale := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        ring
      have hevent :
          (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              Event a Omega ∧
                (∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega)) =
            (fun Omega =>
              ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                pair ∈ insert a s → Event pair Omega) := by
        funext Omega
        apply propext
        constructor
        · intro h pair hpair
          rcases h with ⟨haEvent, hsEvent⟩
          by_cases hpa : pair = a
          · simpa [hpa] using haEvent
          · exact hsEvent pair (by simpa [Finset.mem_insert, hpa] using hpair)
        · intro h
          constructor
          · exact h a (by simp)
          · intro pair hpair
            exact h pair (by simp [hpair])
      simpa [hevent, hconst] using hInter

theorem bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w1 w2 : Fin n₁ × Fin n₂,
                |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
          1 -
            (((Fintype.card
              ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) *
              cpoint) * failureScale) := by
  intro _hCpoint _hcpoint p scale failureScale hp hp_one n₁ n₂ Coeff hPoint
  have h :=
    finite_pair_intersection_aux p cpoint failureScale
      (fun pair Omega => |Coeff pair.1 pair.2 Omega| ≤ Cpoint * scale)
      hp hp_one
      (by
        intro pair
        exact hPoint pair.1 pair.2)
      (Finset.univ :
        Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)))
  simpa [Prod.forall] using h
end UniformDependency1
export UniformDependency1 (bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor)

-- Accepted proof by Shuze Chen; submission de149105-2e0c-4158-b24e-8fffcdaf8ffa.
-- Original SHA-256: eaa875926d4cfc459931c518e80dbf88b3bb7fe3042af387510bb4a0e445fb56.
namespace UniformDependency2
open MatrixCompletion

theorem pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    (β c : ℝ) (n₁ n₂ : ℕ) :
    2 < β → 0 < c → 0 < n₁ → 0 < n₂ →
    (((Fintype.card
        ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
        Real.rpow (↑(max n₁ n₂)) (-(β + 4))) ≤
      c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hβ hc hn₁ hn₂
  let N : ℕ := max n₁ n₂
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hfail_nonneg : 0 ≤ Real.rpow (N : ℝ) (-(β + 4)) :=
    Real.rpow_nonneg (le_of_lt hN_pos) _
  have hcard_nat :
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) ≤ N ^ 4 := by
    have hn₁_le : n₁ ≤ N := Nat.le_max_left n₁ n₂
    have hn₂_le : n₂ ≤ N := Nat.le_max_right n₁ n₂
    have hprod : n₁ * n₂ ≤ N * N := Nat.mul_le_mul hn₁_le hn₂_le
    have hprod2 : (n₁ * n₂) * (n₁ * n₂) ≤ (N * N) * (N * N) :=
      Nat.mul_le_mul hprod hprod
    calc
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂))
          = (n₁ * n₂) * (n₁ * n₂) := by
              simp [Fintype.card_prod]
      _ ≤ (N * N) * (N * N) := hprod2
      _ = N ^ 4 := by ring
  have hcard_real :
      (Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) ≤
        (N : ℝ) ^ 4 := by
    exact_mod_cast hcard_nat
  have hmul :
      ((Fintype.card
          ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
          Real.rpow (N : ℝ) (-(β + 4)) ≤
        (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard_real hc_nonneg) hfail_nonneg
  have hrpow :
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4)) =
        Real.rpow (N : ℝ) (-β) := by
    calc
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))
          = Real.rpow (N : ℝ) (4 : ℝ) *
              Real.rpow (N : ℝ) (-(β + 4)) := by
                exact congrArg
                  (fun t => t * Real.rpow (N : ℝ) (-(β + 4)))
                  (Real.rpow_natCast (N : ℝ) 4).symm
      _ = Real.rpow (N : ℝ) ((4 : ℝ) + (-(β + 4))) := by
                exact (Real.rpow_add hN_pos (4 : ℝ) (-(β + 4))).symm
      _ = Real.rpow (N : ℝ) (-β) := by
                congr 1
                ring
  have htarget :
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) =
        c * Real.rpow (N : ℝ) (-β) := by
    calc
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4)))
          = c * (((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))) := by
              ring
      _ = c * Real.rpow (N : ℝ) (-β) := by
              rw [hrpow]
  simpa [N] using le_trans hmul (le_of_eq htarget)
end UniformDependency2
export UniformDependency2 (pair_coordinate_cardinality_loss_absorbed_by_beta_shift)

end UniformInnerProof

open UniformInnerProof MatrixCompletion

open UniformInnerProof.NeumannProof

-- Accepted proof by Shuze Chen; submission efb1c609-304d-44a8-9852-d3ccb0754f1d.
-- Original source SHA-256: 388e6fcad7d808c2c55e9d2973e27346ef32ac2de8af85ac9a8e07b5c9b31aee.
namespace AdditionalDependency0
open MatrixCompletion
open scoped Classical BigOperators

open MatrixCompletion

open scoped Classical BigOperators

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma abs_cross_sum_le_sqrt_mul_sqrt
    {N r : ℕ} (u : Fin r → Fin N → ℝ) (i a : Fin N) :
    |∑ k : Fin r, u k i * u k a| ≤
      Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
        Real.sqrt (∑ k : Fin r, (u k a) ^ 2) := by
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ ∑ k : Fin r, |u k i * u k a| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin r, |u k i| * |u k a| := by
      simp [abs_mul]
    _ ≤ Real.sqrt (∑ k : Fin r, |u k i| ^ 2) *
          Real.sqrt (∑ k : Fin r, |u k a| ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Fin r))
          (fun k => |u k i|) (fun k => |u k a|))
    _ = Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) := by
      simp [sq_abs]

private lemma cross_sum_abs_le_scale_same_dim
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} (hμ : 1 ≤ μ)
    (hEnergy : ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ)) :
    ∀ i a : Fin N,
      |∑ k : Fin r, u k i * u k a| ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro i a
  have hscale_nonneg : 0 ≤ μ * (r : ℝ) / (N : ℝ) := by positivity
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) :=
          abs_cross_sum_le_sqrt_mul_sqrt u i a
    _ ≤ Real.sqrt (μ * (r : ℝ) / (N : ℝ)) *
          Real.sqrt (μ * (r : ℝ) / (N : ℝ)) := by
      exact mul_le_mul (Real.sqrt_le_sqrt (hEnergy i))
        (Real.sqrt_le_sqrt (hEnergy a)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = μ * (r : ℝ) / (N : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt hscale_nonneg

private lemma cross_sum_abs_le_one
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (hOne : ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ (1 : ℝ)) :
    ∀ i a : Fin N,
      |∑ k : Fin r, u k i * u k a| ≤ (1 : ℝ) := by
  intro i a
  calc
    |∑ k : Fin r, u k i * u k a|
        ≤ Real.sqrt (∑ k : Fin r, (u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (u k a) ^ 2) :=
          abs_cross_sum_le_sqrt_mul_sqrt u i a
    _ ≤ Real.sqrt (1 : ℝ) * Real.sqrt (1 : ℝ) := by
      exact mul_le_mul (Real.sqrt_le_sqrt (hOne i))
        (Real.sqrt_le_sqrt (hOne a)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 1 := by norm_num

private lemma same_dim_scale_le_min_scale
    {n₁ n₂ r : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) {μ₀ : ℝ} (hμ₀ : 1 ≤ μ₀) :
    μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
      μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) ∧
    μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
      μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
  have hA_nonneg : 0 ≤ μ₀ * (r : ℝ) := by positivity
  constructor
  · have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
      exact_mod_cast min_le_left n₁ n₂
    gcongr
  · have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
      exact_mod_cast min_le_right n₁ n₂
    gcongr

private lemma tangent_coordinate_kernel_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
        (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  have hleft :
      leftSingularProjection S (coordinateMatrix i j) a b =
        if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0 := by
    unfold leftSingularProjection coordinateMatrix
    by_cases hbj : b = j
    · rw [Finset.sum_eq_single i]
      · simp [hbj, mul_comm]
      · intro x _hx hx
        simp [hx, hbj]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · rw [Finset.sum_eq_zero]
      · have hjb : ¬ j = b := fun h => hbj h.symm
        simp [hjb]
      · intro x _hx
        simp [hbj]
  have hright :
      rightSingularProjection S (coordinateMatrix i j) a b =
        if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
    unfold rightSingularProjection coordinateMatrix
    by_cases hai : a = i
    · rw [Finset.sum_eq_single j]
      · simp [hai]
      · intro y _hy hy
        simp [hai, hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · rw [Finset.sum_eq_zero]
      · have hia : ¬ i = a := fun h => hai h.symm
        simp [hia]
      · intro y _hy
        simp [hai]
  have htwo :
      twoSidedSingularProjection S (coordinateMatrix i j) a b =
        (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k : Fin r, S.v k j * S.v k b) := by
    unfold twoSidedSingularProjection coordinateMatrix
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [Finset.mul_sum, mul_comm, mul_assoc]
      · intro y _hy hy
        simp [hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro x _hx hx
      simp [hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp [tangentProjection, hleft, hright, htwo]

/-- Source: Candes--Recht 2008, PDF p. 23, equation (6.2), together with the
rectangular convention stated immediately after equations (6.2)--(6.4).

The proof expands `P_T(e_i e_j^*)`, bounds the left and right singular-vector
cross terms by Cauchy--Schwarz from A0 and Bessel, and absorbs `n₁`/`n₂` into
`min(n₁,n₂)`. -/
theorem tangent_coordinate_kernel_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨3, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j a b
  have hEnergy := a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hleft_raw :
      |∑ k : Fin r, S.u k i * S.u k a| ≤ μ₀ * (r : ℝ) / (n₁ : ℝ) :=
    cross_sum_abs_le_scale_same_dim hn₁ hr S.u hμ₀ hEnergy.1 i a
  have hright_raw :
      |∑ k : Fin r, S.v k j * S.v k b| ≤ μ₀ * (r : ℝ) / (n₂ : ℝ) :=
    cross_sum_abs_le_scale_same_dim hn₂ hr S.v hμ₀ hEnergy.2 j b
  have hscale_le := same_dim_scale_le_min_scale hn₁ hn₂ hr hμ₀
  have hleft : |∑ k : Fin r, S.u k i * S.u k a| ≤ scale := by
    exact le_trans hleft_raw hscale_le.1
  have hright : |∑ k : Fin r, S.v k j * S.v k b| ≤ scale := by
    exact le_trans hright_raw hscale_le.2
  have hleft_one : |∑ k : Fin r, S.u k i * S.u k a| ≤ (1 : ℝ) :=
    cross_sum_abs_le_one S.u hOne.1 i a
  have hright_one : |∑ k : Fin r, S.v k j * S.v k b| ≤ (1 : ℝ) :=
    cross_sum_abs_le_one S.v hOne.2 j b
  have hprod :
      |(∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k : Fin r, S.v k j * S.v k b)| ≤ scale := by
    rw [abs_mul]
    calc
      |∑ k : Fin r, S.u k i * S.u k a| *
          |∑ k : Fin r, S.v k j * S.v k b|
          ≤ 1 * scale := by
            exact mul_le_mul hleft_one hright (abs_nonneg _) zero_le_one
      _ = scale := by ring
  have hterm_left :
      |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)| ≤ scale := by
    by_cases h : j = b
    · simpa [h] using hleft
    · simp [h, hscale_nonneg]
  have hterm_right :
      |(if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| ≤ scale := by
    by_cases h : i = a
    · simpa [h] using hright
    · simp [h, hscale_nonneg]
  have hformula := tangent_coordinate_kernel_formula S i j a b
  calc
    |tangentCoordinateKernel S i j a b|
        = |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
            (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0) -
              (∑ k : Fin r, S.u k i * S.u k a) *
                (∑ k : Fin r, S.v k j * S.v k b)| := by
          rw [hformula]
    _ ≤ |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)| +
          |(if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| +
            |(∑ k : Fin r, S.u k i * S.u k a) *
              (∑ k : Fin r, S.v k j * S.v k b)| := by
          have hsub :
              |((if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)) -
                  (∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)| ≤
                |(if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)| +
                  |(∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)| := by
            have h :=
              abs_add_le
                ((if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
                  (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0))
                (-((∑ k : Fin r, S.u k i * S.u k a) *
                    (∑ k : Fin r, S.v k j * S.v k b)))
            simpa [sub_eq_add_neg, abs_neg] using h
          have hsum :=
            abs_add_le (if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0)
              (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0)
          linarith
    _ ≤ scale + scale + scale := by
          linarith
    _ = 3 * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
          dsimp [scale]
          ring
end AdditionalDependency0
export AdditionalDependency0 (tangent_coordinate_kernel_bound_from_a0_min_dim)

-- Accepted proof by Harry_Xu; submission 60f6a168-dca9-478a-8f8c-0d9150f0a711.
-- Original source SHA-256: 3c23fafe2b5d57e0df72565bd1d76d6539ab869a2f057a183f9c05336c8ae468.
namespace AdditionalDependency1
open MatrixCompletion

/-!
Sound `min(n₁,n₂)`-denominator entry sup-norm bound for the conditional middle
base matrix `quadraticAllDistinctMiddleBaseMatrix` of the triple-decoupled
all-distinct quadratic Neumann term.  Each entry is `G_{ω₂}` (bounded by
`innerBound` on the inner-coefficient event) times one tangent-coordinate kernel
`⟪P_T(eᵢeⱼᵀ), e_{w₁}⟫ ≤ Cker·μ₀·(r/min)` (A0).

Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular kernel
convention after eqs (6.2)--(6.4).  Sound `min`-denominator analogue of the
Disproved max-form supplier.
-/

private lemma mid_entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

/-- Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular
`min(n₁,n₂)` kernel convention after eqs (6.2)--(6.4). -/
theorem quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Centry * innerBound * μ₀ *
              ((r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with
    ⟨Cker, hCker, hKernel⟩
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound hib hInner w1
  refine mid_entrySupNorm_le_of_forall_abs_le hn₁ hn₂
    (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
    (Cker * innerBound * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) ?_
  intro i j
  by_cases hsame : (i, j) = w1
  · simp [quadraticAllDistinctMiddleBaseMatrix, hsame]
    positivity
  · have hcoeff :
        |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| ≤
          innerBound := hInner w1 (i, j)
    have hKer :=
      hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j w1.1 w1.2
    have hKer_nonneg :
        0 ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      positivity
    calc
      |quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1 i j|
          = |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| *
              |tangentCoordinateKernel S i j w1.1 w1.2| := by
            simp [quadraticAllDistinctMiddleBaseMatrix, hsame, abs_mul]
      _ ≤ innerBound * (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
          exact mul_le_mul hcoeff hKer (abs_nonneg _) hib
      _ = Cker * innerBound * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
          ring
end AdditionalDependency1
export AdditionalDependency1 (quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim)

-- Accepted proof by Harry_Xu; submission 22de1ebf-2064-4348-bebe-1f65a5e2ddff.
-- Original source SHA-256: cca137a3fff353e6f7f4eb0cb5696e92ff58bcb727054b4cdd74efd06370d3d7.
namespace AdditionalDependency2
open MatrixCompletion

open scoped Classical BigOperators

/-!
Sound `min(n₁,n₂)`-denominator Frobenius bound for the conditional middle base
matrix `quadraticAllDistinctMiddleBaseMatrix` of the triple-decoupled all-distinct
quadratic Neumann term.  Each entry is `G_{ω₂}` (the inner coefficient, bounded
on the inner-coefficient event by `innerBound`) times one tangent-coordinate
kernel `⟪P_T(eᵢeⱼᵀ), e_{w₁}⟫`; the row/column-summed kernel-square is governed by
the diagonal kernel `≤ Cker·μ₀·(r/min)` (A0).

Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular kernel
convention after eqs (6.2)--(6.4).  This is the sound `min`-denominator analogue
of the Disproved max-form supplier; it reuses the kernel-square-sum identity from
the Proved min-dim off-diagonal Frobenius supplier.
-/

namespace MatrixCompletion

private lemma mid_matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma mid_coordinate_projection_kernel_norm_square
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0)
    (i : Fin N) :
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2 =
      ∑ k : Fin r, (u k i) ^ 2 := by
  calc
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2
        = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (u k a * u l a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [horth k l]
    _ = ∑ k : Fin r, (u k i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma mid_leftSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) a b =
      if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0 := by
  unfold leftSingularProjection coordinateMatrix
  by_cases hbj : b = j
  · rw [Finset.sum_eq_single i]
    · simp [hbj]
    · intro x _hx hx
      simp [hx, hbj]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hbj]
    · intro x _hx
      simp [hbj]

private lemma mid_rightSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) a b =
      if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
  unfold rightSingularProjection coordinateMatrix
  by_cases hai : a = i
  · rw [Finset.sum_eq_single j]
    · simp [hai]
    · intro x _hx hx
      simp [hai, hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hai]
    · intro x _hx
      simp [hai]

private lemma mid_twoSidedSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) a b =
      (∑ k : Fin r, S.u k a * S.u k i) *
        (∑ k : Fin r, S.v k j * S.v k b) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Finset.mul_sum, Finset.sum_mul]
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro x _hx hx
    simp [hx]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma mid_tangentProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix i j) a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  simp [tangentProjection, mid_leftSingularProjection_coordinate_apply,
    mid_rightSingularProjection_coordinate_apply,
    mid_twoSidedSingularProjection_coordinate_apply]

private lemma mid_tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, mid_matrixInner_coordinate_right]
  simp [mid_tangentProjection_coordinate_apply, pow_two]

private lemma mid_tangent_coordinate_kernel_apply_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, mid_matrixInner_coordinate_right]
  exact mid_tangentProjection_coordinate_apply S i j a b

private lemma mid_coordinate_projection_square_sum
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : α → ℝ) (Q : β → ℝ) (i : α) (j : β)
    (hPi : P i = ∑ a : α, P a ^ 2)
    (hQj : Q j = ∑ b : β, Q b ^ 2) :
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2 =
      (∑ a : α, P a ^ 2) +
        (∑ b : β, Q b ^ 2) -
          (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
  classical
  let A : ℝ := ∑ a : α, P a ^ 2
  let B : ℝ := ∑ b : β, Q b ^ 2
  have hPi' : P i = A := by simpa [A] using hPi
  have hQj' : Q j = B := by simpa [B] using hQj
  have hPQ : (∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2) = A * B := by
    dsimp [A, B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hPQsq : (∑ a : α, ∑ b : β, (P a * Q b) ^ 2) = A * B := by
    calc
      ∑ a : α, ∑ b : β, (P a * Q b) ^ 2
          = ∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = A * B := hPQ
  have hCrossP : (∑ a : α, 2 * P a * (P a * B)) = 2 * A * B := by
    calc
      ∑ a : α, 2 * P a * (P a * B)
          = ∑ a : α, (2 * B) * P a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
      _ = (2 * B) * (∑ a : α, P a ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [A, mul_assoc, mul_left_comm, mul_comm]
  have hCrossQ : (∑ b : β, 2 * Q b * (A * Q b)) = 2 * A * B := by
    calc
      ∑ b : β, 2 * Q b * (A * Q b)
          = ∑ b : β, (2 * A) * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = (2 * A) * (∑ b : β, Q b ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [B, mul_assoc]
  calc
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2
        = ∑ a : α, ∑ b : β,
            ((if b = j then P a else 0) ^ 2 +
              (if a = i then Q b else 0) ^ 2 +
              (P a * Q b) ^ 2 +
              2 * (if b = j then P a else 0) *
                (if a = i then Q b else 0) -
              2 * (if b = j then P a else 0) * (P a * Q b) -
              2 * (if a = i then Q b else 0) * (P a * Q b)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
    _ = A + B + A * B + 2 * A * B - 2 * A * B - 2 * A * B := by
            simp [hPi', hQj', Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            rw [hPQsq, hCrossP, hCrossQ]
            ring
    _ = A + B - A * B := by ring
    _ = (∑ a : α, P a ^ 2) +
          (∑ b : β, Q b ^ 2) -
            (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
            simp [A, B]

private lemma mid_tangent_coordinate_kernel_square_sum_eq_diagonal
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (tangentCoordinateKernel S i j a b) ^ 2 =
      tangentCoordinateKernel S a b a b := by
  let P : Fin n₁ → ℝ := fun i => ∑ k : Fin r, S.u k a * S.u k i
  let Q : Fin n₂ → ℝ := fun j => ∑ k : Fin r, S.v k j * S.v k b
  have hPnorm : ∑ i : Fin n₁, P i ^ 2 = ∑ k : Fin r, (S.u k a) ^ 2 := by
    have hbase :=
      mid_coordinate_projection_kernel_norm_square S.u S.u_orthonormal a
    calc
      ∑ i : Fin n₁, P i ^ 2
          = ∑ i : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            congr 1
            apply Finset.sum_congr rfl
            intro k _hk
            simp [mul_comm]
      _ = ∑ k : Fin r, (S.u k a) ^ 2 := by
            simpa [pow_two] using hbase
  have hQnorm : ∑ j : Fin n₂, Q j ^ 2 = ∑ k : Fin r, (S.v k b) ^ 2 := by
    have hbase :=
      mid_coordinate_projection_kernel_norm_square S.v S.v_orthonormal b
    simpa [Q, pow_two] using hbase
  have hPa : P a = ∑ k : Fin r, (S.u k a) ^ 2 := by
    simp [P, pow_two]
  have hQb : Q b = ∑ k : Fin r, (S.v k b) ^ 2 := by
    simp [Q, pow_two]
  calc
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (tangentCoordinateKernel S i j a b) ^ 2
        = ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((if j = b then P i else 0) +
              (if i = a then Q j else 0) - P i * Q j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            rw [mid_tangent_coordinate_kernel_apply_formula]
            simp [P, Q, eq_comm]
    _ = (∑ i : Fin n₁, P i ^ 2) +
          (∑ j : Fin n₂, Q j ^ 2) -
            (∑ i : Fin n₁, P i ^ 2) *
              (∑ j : Fin n₂, Q j ^ 2) := by
            exact mid_coordinate_projection_square_sum P Q a b
              (hPa.trans hPnorm.symm) (hQb.trans hQnorm.symm)
    _ = (∑ k : Fin r, (S.u k a) ^ 2) +
          (∑ k : Fin r, (S.v k b) ^ 2) -
            (∑ k : Fin r, (S.u k a) ^ 2) *
              (∑ k : Fin r, (S.v k b) ^ 2) := by
            rw [hPnorm, hQnorm]
    _ = tangentCoordinateKernel S a b a b := by
            rw [mid_tangent_coordinate_kernel_diagonal_formula]

/-- Frobenius-square bound for the middle base matrix: each entry is bounded by
`innerBound · |kernel|`, so the Frobenius square is `≤ innerBound² · Σ kernel²`. -/
private lemma mid_frobeniusNormSq_base_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ)
    (hib : 0 ≤ innerBound)
    (hInner : QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound)
    (w1 : Fin n₁ × Fin n₂) :
    frobeniusNormSq (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
      innerBound ^ 2 *
        (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) := by
  unfold frobeniusNormSq
  calc
    ∑ i : Fin n₁, ∑ j : Fin n₂,
        (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1 i j) ^ 2
        ≤ ∑ i : Fin n₁, ∑ j : Fin n₂,
            innerBound ^ 2 * (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hsame : (i, j) = w1
          · simp [quadraticAllDistinctMiddleBaseMatrix, hsame]
            positivity
          · have hcoeff :
                |quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)| ≤
                  innerBound := hInner w1 (i, j)
            have hcoeffsq :
                (quadraticAllDistinctInnerCoefficient Omega3 S p w1 (i, j)) ^ 2 ≤
                  innerBound ^ 2 := by
              have := sq_le_sq' (neg_le_of_abs_le hcoeff) (le_of_abs_le hcoeff)
              simpa using this
            have hmul :=
              mul_le_mul_of_nonneg_right hcoeffsq
                (sq_nonneg (tangentCoordinateKernel S i j w1.1 w1.2))
            simpa [quadraticAllDistinctMiddleBaseMatrix, hsame, pow_two,
              mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = innerBound ^ 2 *
        (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]

end MatrixCompletion

open MatrixCompletion

/-- Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 eq (6.22); rectangular
`min(n₁,n₂)` kernel convention after eqs (6.2)--(6.4). -/
theorem quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with
    ⟨Cker, hCker_pos, hKernel⟩
  refine ⟨Real.sqrt Cker, Real.sqrt_pos.2 hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound hib hInner w1
  set kernelScale : ℝ := μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hkernelScale
  have hKernelScale_nonneg : 0 ≤ kernelScale := by
    rw [hkernelScale]; positivity
  have hCker_nonneg : 0 ≤ Cker := le_of_lt hCker_pos
  have hsqBase :=
    mid_frobeniusNormSq_base_le S Omega3 p innerBound hib hInner w1
  have hKernelSq :
      (∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2) ≤
        Cker * kernelScale := by
    have hsum :=
      mid_tangent_coordinate_kernel_square_sum_eq_diagonal S w1.1 w1.2
    have hdiag :=
      hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1.1 w1.2 w1.1 w1.2
    calc
      ∑ i : Fin n₁, ∑ j : Fin n₂,
          (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2
          = tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2 := hsum
      _ ≤ |tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2| := le_abs_self _
      _ ≤ Cker * kernelScale := by
          simpa [hkernelScale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            using hdiag
  have hsq :
      frobeniusNormSq (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
        innerBound ^ 2 * (Cker * kernelScale) := by
    exact le_trans hsqBase
      (mul_le_mul_of_nonneg_left hKernelSq (sq_nonneg innerBound))
  have hsqrt :
      frobeniusNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
        Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) := by
    unfold frobeniusNorm
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_eq :
      Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) =
        Real.sqrt Cker * innerBound * Real.sqrt kernelScale := by
    rw [Real.sqrt_mul (sq_nonneg innerBound)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg hib]
    rw [Real.sqrt_mul hCker_nonneg]
    ring
  calc
    frobeniusNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
        ≤ Real.sqrt (innerBound ^ 2 * (Cker * kernelScale)) := hsqrt
    _ = Real.sqrt Cker * innerBound * Real.sqrt kernelScale := hsqrt_eq
    _ = Real.sqrt Cker * innerBound *
          Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
          rw [hkernelScale]
end AdditionalDependency2
export AdditionalDependency2 (quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim)

-- Accepted proof by tianyipeng; submission c7b14aa7-0692-48b9-81fa-97c647b0b6c2.
-- Original source SHA-256: 51226d042007e89211c7e26b185225fac8c2f35b137949171ec10b22dd6bab4f.
namespace AdditionalDependency3
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  unfold centeredSamplingFluctuation centeredIndicator
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, samplingProjection]
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 w2 : Fin n₁ × Fin n₂) :
    quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega3 p
          (quadraticAllDistinctInnerBaseMatrix S w1 w2)) := by
  unfold quadraticAllDistinctInnerCoefficient matrixEntrySum
  simp only [csf_apply, quadraticAllDistinctInnerBaseMatrix, Prod.mk.eta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1 ∨ w = w2
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
end AdditionalDependency3
export AdditionalDependency3 (quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation)

-- Accepted proof by tianyipeng; submission 5bcfd5b5-8cf4-4698-aea1-1030ac042066.
-- Original source SHA-256: 4ad137cf253b9b49cd124d48d2b65fb46f2670004a9077c759d5a3fae43cf780.
namespace AdditionalDependency4
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  unfold centeredSamplingFluctuation centeredIndicator
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, samplingProjection]
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
  unfold quadraticAllDistinctMiddleCoefficient matrixEntrySum
  simp only [csf_apply, quadraticAllDistinctMiddleBaseMatrix, Prod.mk.eta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
end AdditionalDependency4
export AdditionalDependency4 (quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation)

-- Accepted proof by Shuze Chen; submission e376cb1a-4c01-4b14-ad56-4b8dee9024e9.
-- Original source SHA-256: 74b1f628dad17fe9b4d414aa973e00906ccd5cf78a45ce55d5643be9ece1ce92.
namespace AdditionalDependency5
open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma sum_bernoulliObservationWeight_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} (_hp : 0 ≤ p) (_hp_one : p ≤ 1) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma bernoulliEventProb_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ bernoulliEventProb p Event := by
  unfold bernoulliEventProb
  apply Finset.sum_nonneg
  intro Omega _
  by_cases hEvent : Event Omega
  · simp [hEvent, bernoulliObservationWeight_nonneg hp hp_one Omega]
  · simp [hEvent]

private lemma bernoulliEventProb_le_one
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event ≤ 1 := by
  have hle :
      bernoulliEventProb p Event ≤
        ∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega := by
    unfold bernoulliEventProb
    apply Finset.sum_le_sum
    intro Omega _
    by_cases hEvent : Event Omega
    · simp [hEvent]
    · simp [hEvent, bernoulliObservationWeight_nonneg hp hp_one Omega]
  simpa [sum_bernoulliObservationWeight_eq_one hp hp_one] using hle

private lemma bernoulliPairEventProb_as_conditional_sum
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliPairEventProb p EventPair =
      ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega2 *
          bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) := by
  unfold bernoulliPairEventProb bernoulliEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega2 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega1 _
  by_cases hEvent : EventPair Omega1 Omega2
  · simp [hEvent]
    ring
  · simp [hEvent]

theorem bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
    {n₁ n₂ : ℕ} (p cMarg cCond scale : ℝ)
    (EventMarg : Finset (Fin n₁ × Fin n₂) → Prop)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    0 ≤ cCond * scale →
    bernoulliEventProb p EventMarg ≥ 1 - cMarg * scale →
    (∀ Omega2,
      EventMarg Omega2 →
        bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) ≥
          1 - cCond * scale) →
    bernoulliPairEventProb p EventPair ≥ 1 - (cCond + cMarg) * scale := by
  intro hp hp_one hCondFailureNonneg hMarg hCond
  let marginalProb : ℝ := bernoulliEventProb p EventMarg
  let condFailure : ℝ := cCond * scale
  let margFailure : ℝ := cMarg * scale
  have hmarg_le_one : marginalProb ≤ 1 := by
    exact bernoulliEventProb_le_one hp hp_one EventMarg
  have hmarg_nonneg : 0 ≤ marginalProb := by
    exact bernoulliEventProb_nonneg hp hp_one EventMarg
  have hmargFailureNonneg : 0 ≤ margFailure := by
    have hle_one : 1 - margFailure ≤ 1 := le_trans hMarg hmarg_le_one
    linarith
  have hpair_lower :
      bernoulliPairEventProb p EventPair ≥
        marginalProb * (1 - condFailure) := by
    rw [bernoulliPairEventProb_as_conditional_sum]
    have hsum_lower :
        (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
            (if EventMarg Omega2 then
              bernoulliObservationWeight p Omega2 * (1 - condFailure)
            else 0)) ≤
          ∑ Omega2 : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega2 *
              bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) := by
      apply Finset.sum_le_sum
      intro Omega2 _
      by_cases hM : EventMarg Omega2
      · have hw := bernoulliObservationWeight_nonneg hp hp_one Omega2
        have hc :
            1 - condFailure ≤
              bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) := by
          simpa [condFailure] using hCond Omega2 hM
        simp [hM]
        exact mul_le_mul_of_nonneg_left hc hw
      · have hw := bernoulliObservationWeight_nonneg hp hp_one Omega2
        have hprob :
            0 ≤ bernoulliEventProb p
              (fun Omega1 => EventPair Omega1 Omega2) :=
          bernoulliEventProb_nonneg hp hp_one _
        simp [hM]
        exact mul_nonneg hw hprob
    have hsum_eq :
        (∑ Omega2 : Finset (Fin n₁ × Fin n₂),
            (if EventMarg Omega2 then
              bernoulliObservationWeight p Omega2 * (1 - condFailure)
            else 0)) =
          marginalProb * (1 - condFailure) := by
      unfold marginalProb bernoulliEventProb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Omega2 _
      by_cases hM : EventMarg Omega2
      · simp [hM]
      · simp [hM]
    simpa [hsum_eq] using hsum_lower
  have hscalar :
      marginalProb * (1 - condFailure) ≥
        1 - (cCond + cMarg) * scale := by
    have htarget :
        1 - (cCond + cMarg) * scale =
          1 - condFailure - margFailure := by
      simp [condFailure, margFailure]
      ring
    rw [htarget]
    by_cases hfactor : 0 ≤ 1 - condFailure
    · have hprod_lower :
          (1 - margFailure) * (1 - condFailure) ≤
            marginalProb * (1 - condFailure) := by
        exact mul_le_mul_of_nonneg_right hMarg hfactor
      have hcross :
          1 - condFailure - margFailure ≤
            (1 - margFailure) * (1 - condFailure) := by
        nlinarith [hCondFailureNonneg, hmargFailureNonneg]
      exact le_trans hcross hprod_lower
    · have hfactor_nonpos : 1 - condFailure ≤ 0 := le_of_lt (lt_of_not_ge hfactor)
      have hprod_ge_factor :
          1 - condFailure ≤ marginalProb * (1 - condFailure) := by
        have hmul :=
          mul_le_mul_of_nonpos_right hmarg_le_one hfactor_nonpos
        simpa using hmul
      have htarget_le_factor :
          1 - condFailure - margFailure ≤ 1 - condFailure := by
        linarith
      exact le_trans htarget_le_factor hprod_ge_factor
  exact le_trans hscalar hpair_lower
end AdditionalDependency5
export AdditionalDependency5 (bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg)

-- Accepted proof by Shuze Chen; submission c6296928-627d-4adf-a53d-976bd703a8a0.
-- Original source SHA-256: 685b7961fff6c5c4d9523a52b51ed00f53b117d410e5daa84d63cbb6df6af5a5.
namespace AdditionalDependency6
open MatrixCompletion


open MatrixCompletion

theorem sample_ratio_between_zero_and_one
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ∧
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by
      exact mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
    have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast hm
    rw [div_le_iff₀ hden_pos]
    simpa using hnum_le_den
end AdditionalDependency6
export AdditionalDependency6 (sample_ratio_between_zero_and_one)

-- Accepted proof by Shuze Chen; submission 08e69fee-20a9-45d1-8132-0f6828ef53af.
-- Original source SHA-256: 0129d75d07f9bdff30739725da283a35be5daf6e3b20b01008bc2ba21b093a4f.
namespace AdditionalDependency7
open MatrixCompletion

/-- Specialize the reusable two-copy Bernoulli product lift to the
all-distinct middle coefficient transfer from the inner coefficient event. -/
theorem quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctInnerCoefficientBound Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner) * Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCcond hccond
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam _hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    Cinner cinner _hCinner _hcinner hInnerProb hCondProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hFailureNonneg :
      0 ≤ ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hmax_pos_nat : 0 < max n₁ n₂ :=
      lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hmax_pos : 0 < (↑(max n₁ n₂) : ℝ) := by
      exact_mod_cast hmax_pos_nat
    exact mul_nonneg (le_of_lt hccond)
      (le_of_lt (Real.rpow_pos_of_pos hmax_pos (-β)))
  exact
    bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
      p cinner ccond (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega3 =>
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p
          (Cinner * Real.rpow lam (-((1 : ℝ) / 2))))
      (fun Omega2 Omega3 =>
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          ((Ccond * Cinner) * Real.rpow lam (-1)))
      hp.1 hp.2 hFailureNonneg hInnerProb hCondProb
end AdditionalDependency7
export AdditionalDependency7 (quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound)

-- Adapted from Shuze Chen, accepted submission 69536e3c-760e-41e8-8a4f-c0333b2078b6.
-- Use the same unshifted beta in the density and scale; raw-tail shifting is handled separately.
theorem middle_scale_absorb
    {β lam : ℝ} {n₁ n₂ r m : ℕ} {μ₀ innerBound Centry Cfro : ℝ}
    (hβ : 2 < β) (hlam : 1 ≤ lam)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hib : 0 ≤ innerBound)
    (hCentry : 0 < Centry) (hCfro : 0 < Cfro)
    (hm_pos : 0 < (m : ℝ))
    (hdensity :
      (m : ℝ) ≥
        lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
          (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
            ((β) * Real.log (↑(max n₁ n₂)))) :
    Real.sqrt
          (((β) * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * innerBound *
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))) +
      (((β) * Real.log (↑(max n₁ n₂))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (↑(min n₁ n₂)))) ≤
      (Cfro + Centry) * innerBound *
          Real.rpow lam (-((1 : ℝ) / 2)) := by
  set N : ℕ := max n₁ n₂ with hN
  set d : ℕ := min n₁ n₂ with hd
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hd_pos_nat : 0 < d := lt_min hn₁ hn₂
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hnprod_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hlam_pos : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge_one
  have hβ4_pos : 0 < β := by linarith
  have hp_pos : 0 < (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  -- The energy quantity `A = μ₀ N r (β) logN / m`.
  set A : ℝ := (μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ))) / (m : ℝ)
    with hA
  have hA_nonneg : 0 ≤ A := by rw [hA]; positivity
  -- density gives A ≤ 1/lam, via μ₀^{4/3}, r^{4/3} ≥ μ₀ r.
  have hrpow_mu0 : μ₀ ≤ Real.rpow μ₀ ((4 : ℝ) / 3) := by
    calc μ₀ = Real.rpow μ₀ 1 := (Real.rpow_one μ₀).symm
      _ ≤ Real.rpow μ₀ ((4:ℝ)/3) := by
          apply Real.rpow_le_rpow_of_exponent_le hμ₀
          norm_num
  have hrpow_r : (r : ℝ) ≤ Real.rpow (r : ℝ) ((4 : ℝ) / 3) := by
    calc (r : ℝ) = Real.rpow (r : ℝ) 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow (r : ℝ) ((4:ℝ)/3) := by
          apply Real.rpow_le_rpow_of_exponent_le hr_ge_one
          norm_num
  have hdensity_weak :
      lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ)) ≤ (m : ℝ) := by
    have hbase_nonneg :
        0 ≤ lam * (N : ℝ) * ((β) * Real.log (N : ℝ)) := by positivity
    have hstep :
        lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ)) ≤
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (N : ℝ) *
            Real.rpow (r : ℝ) ((4 : ℝ) / 3) * ((β) * Real.log (N : ℝ)) := by
      have h1 : μ₀ * (r : ℝ) ≤
          Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r : ℝ) ((4:ℝ)/3) := by
        apply mul_le_mul hrpow_mu0 hrpow_r (le_of_lt hr_pos)
        exact Real.rpow_nonneg hμ₀_pos.le _
      nlinarith [hlog_nonneg, hN_pos.le, hlam_pos.le, hβ4_pos.le, hbase_nonneg,
        Real.rpow_nonneg hμ₀_pos.le ((4:ℝ)/3),
        Real.rpow_nonneg hr_pos.le ((4:ℝ)/3)]
    calc lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ))
        ≤ lam * Real.rpow μ₀ ((4 : ℝ) / 3) * (N : ℝ) *
            Real.rpow (r : ℝ) ((4 : ℝ) / 3) * ((β) * Real.log (N : ℝ)) := hstep
      _ ≤ (m : ℝ) := by rw [hN] at hdensity ⊢; linarith [hdensity]
  have hA_le_inv_lam : A ≤ lam⁻¹ := by
    rw [hA, div_le_iff₀ hm_pos]
    rw [inv_mul_eq_div, le_div_iff₀ hlam_pos]
    calc μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ)) * lam
        = lam * μ₀ * (N : ℝ) * (r : ℝ) * ((β) * Real.log (N : ℝ)) := by ring
      _ ≤ (m : ℝ) := hdensity_weak
  -- λ^{-1/2} as a square root of λ⁻¹.
  have hrpow_neg_half : Real.rpow lam (-((1 : ℝ) / 2)) = Real.sqrt lam⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one lam,
      ← Real.rpow_mul hlam_pos.le]
    norm_num
  have hsqrtA_le : Real.sqrt A ≤ Real.rpow lam (-((1 : ℝ) / 2)) := by
    rw [hrpow_neg_half]
    exact Real.sqrt_le_sqrt hA_le_inv_lam
  have hA_le_one : A ≤ 1 := le_trans hA_le_inv_lam (by
    rw [inv_le_one_iff₀]; right; exact hlam)
  have hA_le_sqrtA : A ≤ Real.sqrt A := by
    by_cases hAz : A = 0
    · rw [hAz, Real.sqrt_zero]
    · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hAz)
      have hsq : A ^ 2 ≤ (Real.sqrt A) ^ 2 := by
        rw [Real.sq_sqrt hA_nonneg]; nlinarith [hA_nonneg, hA_le_one]
      exact (sq_le_sq₀ hA_nonneg (Real.sqrt_nonneg A)).mp hsq
  have hA_le_rpow : A ≤ Real.rpow lam (-((1 : ℝ) / 2)) :=
    le_trans hA_le_sqrtA hsqrtA_le
  -- frobTerm = √((β)logN/p) · Cfro innerBound √(μ₀r/d)
  -- = Cfro innerBound · √A.
  have hlog_div_eq :
      ((β) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₀ * ((r : ℝ) / (d : ℝ))) = A := by
    rw [hA]
    have hdN : (d : ℝ) * (N : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      rw [hd, hN]
      have hnat : min n₁ n₂ * max n₁ n₂ = n₁ * n₂ := min_mul_max n₁ n₂
      exact_mod_cast hnat
    field_simp
    nlinarith [hdN, hm_pos, hd_pos, hN_pos, hnprod_pos]
  have hfrob_sqrt :
      Real.sqrt
          (((β) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ))) = Real.sqrt A := by
    rw [← Real.sqrt_mul (by positivity), hlog_div_eq]
  -- FROB TERM ≤ Cfro · innerBound · √A ≤ Cfro · innerBound · λ^{-1/2}
  have hfrob_term :
      Real.sqrt
          (((β) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * innerBound *
            Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) ≤
        Cfro * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := by
    have hrw :
        Real.sqrt
            (((β) * Real.log (N : ℝ)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) =
          Cfro * innerBound * Real.sqrt A := by
      rw [← hfrob_sqrt]; ring
    rw [hrw]
    have hbase_nonneg : 0 ≤ Cfro * innerBound := by positivity
    exact mul_le_mul_of_nonneg_left hsqrtA_le hbase_nonneg
  -- RANGE TERM = A · Centry · innerBound ≤ Centry · innerBound · λ^{-1/2}
  have hrange_term :
      (((β) * Real.log (N : ℝ)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * innerBound * μ₀ *
            ((r : ℝ) / (d : ℝ))) ≤
        Centry * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := by
    have hrw :
        (((β) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * innerBound * μ₀ *
              ((r : ℝ) / (d : ℝ))) =
          Centry * innerBound * A := by
      rw [← hlog_div_eq]; ring
    rw [hrw]
    have hbase_nonneg : 0 ≤ Centry * innerBound := by positivity
    exact mul_le_mul_of_nonneg_left hA_le_rpow hbase_nonneg
  -- combine
  have hsum := add_le_add hfrob_term hrange_term
  have hgoal :
      Real.sqrt
            (((β) * Real.log (N : ℝ)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (d : ℝ)))) +
        (((β) * Real.log (N : ℝ)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * innerBound * μ₀ *
              ((r : ℝ) / (d : ℝ))) ≤
        (Cfro + Centry) * innerBound *
            Real.rpow lam (-((1 : ℝ) / 2)) := by
    calc _ ≤ Cfro * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) +
              Centry * innerBound * Real.rpow lam (-((1 : ℝ) / 2)) := hsum
      _ = (Cfro + Centry) * innerBound *
            Real.rpow lam (-((1 : ℝ) / 2)) := by ring
  rw [hN, hd] at hgoal ⊢
  convert hgoal using 2

end StructuralMiddleProof

open MatrixCompletion StructuralMiddleProof
open StructuralMiddleProof.UniformInnerProof StructuralMiddleProof.UniformInnerProof.NeumannProof

theorem solution :
    ∃ Cmid cmid : ℝ, 0 < Cmid ∧ 0 < cmid ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cmid * Real.rpow lam (-1))) ≥
          1 - cmid * Real.rpow (↑(max n₁ n₂)) (-β) := by
  classical
  rcases shifted_structural_tail with ⟨Cinner, cinner, hCinner, hcinner, hInnerPoint⟩
  rcases quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hEntry⟩
  rcases quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hFrob⟩
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  let Ccond : ℝ := (3 * Cbern) * (Cfro + Centry)
  have hCcond : 0 < Ccond := by dsimp [Ccond]; positivity
  rcases quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
      Ccond (cbern + 1) hCcond (by positivity) with
    ⟨Cstep, cstep, hCstep, hcstep, hPair⟩
  refine ⟨Cstep * Cinner, cstep + cinner, by positivity, by positivity, ?_⟩
  intro beta lam hbeta hlam n1 n2 r m M mu0 mu1 S
    hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample
  let p : ℝ := (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))
  let N : ℝ := (max n1 n2 : ℕ)
  let ib : ℝ := Cinner * Real.rpow lam (-((1 : ℝ) / 2))
  have hp : 0 ≤ p ∧ p ≤ 1 := sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm
  have hlam0 : 0 < lam := by linarith
  have hib : 0 ≤ ib := by dsimp [ib]; positivity
  have hInnPoint := hInnerPoint beta lam hbeta hlam n1 n2 r m M mu0 mu1 S
    hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample
    (fun Omega3 w1 w2 =>
      quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
        Omega3 S p w1 w2)
  have hInnerUniform :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      Cinner cinner hCinner hcinner p (Real.rpow lam (-((1 : ℝ) / 2)))
      (Real.rpow N (-(beta + 4))) hp.1 hp.2 n1 n2
      (fun w1 w2 Omega3 => quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2)
      hInnPoint
  have hInnerCard := pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    beta cinner n1 n2 hbeta hcinner hn1 hn2
  have hInnerProb :
      bernoulliEventProb p
        (fun Omega3 => QuadraticAllDistinctInnerCoefficientBound Omega3 S p ib) ≥
      1 - cinner * Real.rpow N (-beta) := by
    apply le_trans ?_ hInnerUniform
    dsimp [N] at *
    linarith
  apply hPair beta lam hbeta hlam n1 n2 r m M mu0 mu1 S
    hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample Cinner cinner hCinner hcinner hInnerProb
  intro Omega3 hInner
  let e : ℝ := Centry * ib * mu0 * ((r : ℝ) / (min n1 n2 : ℕ))
  let f : ℝ := Cfro * ib * Real.sqrt (mu0 * ((r : ℝ) / (min n1 n2 : ℕ)))
  rcases Nat.lt_or_ge (max n1 n2) 2 with hsmall | hbig
  · have hN1 : max n1 n2 = 1 := by omega
    have hpow : Real.rpow N (-beta) = 1 := by
      dsimp only [N]
      rw [hN1]
      simp
    have hprob : 0 ≤ bernoulliEventProb p
        (fun Omega2 => QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          ((Ccond * Cinner) * Real.rpow lam (-1))) := by
      unfold bernoulliEventProb
      apply Finset.sum_nonneg
      intro Omega2 _
      split_ifs
      · unfold bernoulliObservationWeight
        exact mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _)
      · exact le_rfl
    change 1 - (cbern + 1) * Real.rpow N (-beta) ≤ _
    rw [hpow, mul_one]
    exact (by linarith : 1 - (cbern + 1) ≤ 0).trans hprob
  have hN2 : (2 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hbig
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hmu00 : 0 < mu0 := by linarith
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hbeta0 : 0 < beta := by linarith
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le
    (mul_pos (mul_pos (mul_pos (mul_pos hlam0 (Real.rpow_pos_of_pos hmu00 _)) hN0)
      (Real.rpow_pos_of_pos hr0 _)) (mul_pos hbeta0 hlog)) hsample
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hAbsorb := middle_scale_absorb (β := beta) (lam := lam)
    (n₁ := n1) (n₂ := n2) (r := r) (m := m) (μ₀ := mu0)
    (innerBound := ib) (Centry := Centry) (Cfro := Cfro)
    hbeta hlam hn1 hn2 hr hmu0 hib hCentry hCfro hmpos hsample
  have hAbsorb' :
      Real.sqrt ((beta * Real.log N) / p) * f +
        ((beta * Real.log N) / p) * e ≤
      (Cfro + Centry) * ib * Real.rpow lam (-((1 : ℝ) / 2)) := by
    simpa only [e, f, p, N] using hAbsorb
  have hhalf : Real.rpow lam (-((1 : ℝ) / 2)) *
      Real.rpow lam (-((1 : ℝ) / 2)) = Real.rpow lam (-1) := by
    convert (Real.rpow_add hlam0 (-((1 : ℝ) / 2)) (-((1 : ℝ) / 2))).symm using 1 <;> norm_num
  have hscale :
      Cbern * (Real.sqrt (((beta + 4) * Real.log N) / p) * f +
        (((beta + 4) * Real.log N) / p) * e) ≤
      (Ccond * Cinner) * Real.rpow lam (-1) := by
    apply le_trans (shifted_bernstein_scale Cbern e f beta (Real.log N) p
      hCbern.le he hf hbeta hlog.le hp.1)
    calc (3 * Cbern) * (Real.sqrt ((beta * Real.log N) / p) * f +
          ((beta * Real.log N) / p) * e)
        ≤ (3 * Cbern) * ((Cfro + Centry) * ib * Real.rpow lam (-((1 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hAbsorb' (by positivity)
      _ = (Ccond * Cinner) * (Real.rpow lam (-((1 : ℝ) / 2)) *
          Real.rpow lam (-((1 : ℝ) / 2))) := by dsimp [Ccond, ib]; ring
      _ = (Ccond * Cinner) * Real.rpow lam (-1) := by rw [hhalf]
  have hpoint : ∀ w1 w2 : Fin n1 × Fin n2,
      bernoulliEventProb p
        (fun Omega2 => |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
          (Ccond * Cinner) * Real.rpow lam (-1)) ≥
        1 - cbern * Real.rpow N (-(beta + 4)) := by
    intro w1 _w2
    have hraw := hBernstein (beta + 4) (by linarith) n1 n2 m hn1 hn2 hm
      (fun Omega2 => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
      (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) e f
      (fun Omega2 => quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
        Omega2 Omega3 S p w1)
      (hEntry n1 n2 r M mu0 S hn1 hn2 hr hmu0 hA0 Omega3 p ib hib hInner w1)
      (hFrob n1 n2 r M mu0 S hn1 hn2 hr hmu0 hA0 Omega3 p ib hib hInner w1)
    apply le_trans hraw
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega2 hOmega
    exact hOmega.trans hscale
  have hUniform :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      (Ccond * Cinner) cbern (by positivity) hcbern p (Real.rpow lam (-1))
      (Real.rpow N (-(beta + 4))) hp.1 hp.2 n1 n2
      (fun w1 _w2 Omega2 => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
      hpoint
  have hcard := pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    beta cbern n1 n2 hbeta hcbern hn1 hn2
  have hMono :
      bernoulliEventProb p
        (fun Omega2 => ∀ w1 w2 : Fin n1 × Fin n2,
          |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
            (Ccond * Cinner) * Real.rpow lam (-1)) ≤
      bernoulliEventProb p
        (fun Omega2 => QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          ((Ccond * Cinner) * Real.rpow lam (-1))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega2 hOmega w1
    exact hOmega w1 w1
  have hpow0 : 0 ≤ Real.rpow N (-beta) := Real.rpow_nonneg (by linarith) _
  refine le_trans (le_trans ?_ hUniform) hMono
  dsimp [N] at *
  nlinarith

#print axioms solution
