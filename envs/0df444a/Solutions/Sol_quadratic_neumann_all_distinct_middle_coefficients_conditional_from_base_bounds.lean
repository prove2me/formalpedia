-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:17:27.009039+00:00
-- url     : https://prove2.me/submissions/637fc15d-4c60-4f66-9c22-4a8af72768b4

import Mathlib
import Definitions.Def_matrix_completion_neumann

set_option autoImplicit false

namespace MiddleProof

-- Accepted proof by Aphrodite; submission c878d05d-e191-47c8-a2bb-113f888b7985.
-- Original source SHA-256: 807732c32c851f542349b627f3ade5c5fe48726d82384913e3e5f8ce5023430f.
namespace MiddleDependency0
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
end MiddleDependency0
export MiddleDependency0 (bernoulli_powerset_expectation_prod_factor)

-- Accepted proof by Aphrodite; submission 50cd47e2-8a2e-4eb1-9724-8f9afa5dfe28.
-- Original source SHA-256: eed308f01ca5e9b1db71c6c7b2f33f22a6fc1d587d7084b40683592e968e2374.
namespace MiddleDependency1
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
end MiddleDependency1
export MiddleDependency1 (centered_sampling_coefficient_mgf_factorization)

-- Accepted proof by Aphrodite; submission 0ff2689a-aa4a-42ae-8398-bffa9555324d.
-- Original source SHA-256: 404efc41ced0363638d3bab01aafc0f14fa0d6d55d7d5a65459964e616f612aa.
namespace MiddleDependency2
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
end MiddleDependency2
export MiddleDependency2 (exp_le_quad)

-- Accepted proof by Aphrodite; submission a96f36f9-5621-4e58-9efd-849fc99fb54e.
-- Original source SHA-256: e566acfae54e24a4c7663f15865555055e2f1415700a081777b9ac23bb3ad8bb.
namespace MiddleDependency3
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
end MiddleDependency3
export MiddleDependency3 (two_point_bernstein_mgf)

-- Accepted proof by Aphrodite; submission 03179121-d9f3-4e8d-b5ad-44627a812696.
-- Original source SHA-256: 359ea8d26c6c0cd9c8ed0168cabdc670499635c486b3cf38bd2737add8a60c11.
namespace MiddleDependency4
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
end MiddleDependency4
export MiddleDependency4 (centered_sampling_coefficient_bernstein_mgf)

-- Accepted proof by Aphrodite; submission babaa216-33ba-4373-96d9-45e3064a4981.
-- Original source SHA-256: 486d0a8537415d344ec7f02f1ef24202651c4e8c60a8bfec693ab2b9a33c9299.
namespace MiddleDependency5
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
end MiddleDependency5
export MiddleDependency5 (rpow_mul_exp_neg_le)

-- Accepted proof by Aphrodite; submission 1f271913-3fe3-474b-9c0f-917cda8b82d1.
-- Original source SHA-256: 8d533ed97bc218a293100783d6dd26228b4df93577f061b1f24a4e05fe65ba3d.
namespace MiddleDependency6
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
end MiddleDependency6
export MiddleDependency6 (bernoulli_moment_from_two_sided_mgf)

-- Accepted proof by Aphrodite; submission fac29f89-d88a-4043-9f3c-bb4fee69d7b0.
-- Original source SHA-256: d7ae1a6e5e4ddb04cd2c2fc5e67ebc5448dd634dd5674f656833e30482b92a05.
namespace MiddleDependency7
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
end MiddleDependency7
export MiddleDependency7 (scalar_centered_sampling_qnorm_rosenthal_estimate)

-- Accepted proof by Aphrodite; submission 6de2815a-d3a1-4bb4-a454-6ae919754d29.
-- Original source SHA-256: b5d8af983d064e499458ab023a316144d4a6d86f329ffe1869c77ef1fc3b968f.
namespace MiddleDependency8
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
end MiddleDependency8
export MiddleDependency8 (scalar_centered_sampling_qmoment_bernstein_estimate)

-- Accepted proof by Aphrodite; submission 03ca17ec-8750-4cd9-a80a-9e54a267d3ea.
-- Original source SHA-256: f3af4dceb03e74479f1b0af3335b16d58781c105d0abbff2be63a90c0d4d4fb5.
namespace MiddleDependency9
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
end MiddleDependency9
export MiddleDependency9 (scalar_centered_sampling_markov_tail_from_qmoment_bound)

-- Accepted proof by Aphrodite; submission 0b5156fe-a2eb-4ccc-8893-87aa851fcc00.
-- Original source SHA-256: 69759f1182e011602b3a15ea6c9a1eb39c1812855a700e70fea2fa933ff1deb4.
namespace MiddleDependency10
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
end MiddleDependency10
export MiddleDependency10 (scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales)

-- Accepted proof by Aphrodite; submission 92450e05-ef72-48f0-a199-1bf06f7a30f6.
-- Original source SHA-256: 077035308a8f6d51b388f05474e0b1e76837e4b1535eec00b5c212d81c30947e.
namespace MiddleDependency11
open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 400000

namespace Prove10855

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- `1 ≤ β log n` for `β > 2`, `n ≥ 2`. -/
theorem one_le_beta_log (β n : ℝ) (hβ : 2 < β) (hn : 2 ≤ n) (hlogpos : 0 < Real.log n) :
    (1:ℝ) ≤ β * Real.log n := by
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have h4 : (1:ℝ) < Real.log 4 := by
    have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [hlog2n, hlogpos, h4, hlog4]

/-- `lam^(-1/2) = 1/√lam`. -/
theorem rpow_neg_half (lam : ℝ) (h : 0 < lam) : Real.rpow lam (-((1:ℝ)/2)) = 1 / Real.sqrt lam := by
  rw [Real.sqrt_eq_rpow]
  show lam ^ (-((1:ℝ)/2)) = 1 / lam ^ ((1:ℝ)/2)
  rw [Real.rpow_neg (le_of_lt h), inv_eq_one_div]

/-- `lam^(-1) = lam^(-1/2) * lam^(-1/2)`. -/
theorem rpow_neg_one_split (lam : ℝ) (h : 0 < lam) :
    Real.rpow lam (-1) = Real.rpow lam (-((1:ℝ)/2)) * Real.rpow lam (-((1:ℝ)/2)) := by
  show lam ^ (-1 : ℝ) = lam ^ (-((1:ℝ)/2)) * lam ^ (-((1:ℝ)/2))
  rw [← Real.rpow_add h]; norm_num

end Prove10855

open Prove10855 in
/-- `inner_scaled_scalar_bernstein_lambda_scale_absorption`. -/
theorem inner_scaled_scalar_bernstein_lambda_scale_absorption
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ Cinner : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 0 < Cinner →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) ≤
          (Cpoint * Cinner) * Real.rpow lam (-1) := by
  intro hCbern hCentry hCfro
  refine ⟨Cbern * (Cfro + Centry), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ Cinner hn₁ hn₂ hr hm hμ₀ hCinner hsample
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn_def
  set L : ℝ := β * Real.log n with hL_def
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  set x : ℝ := μ₀ * (r:ℝ) with hx_def
  have hx1 : (1:ℝ) ≤ x := by rw [hx_def]; nlinarith
  have hxpos : (0:ℝ) < x := by linarith
  -- lam^(-1/2) value
  have hlh : Real.rpow lam (-((1:ℝ)/2)) = 1 / Real.sqrt lam := rpow_neg_half lam hlam0
  have hsqrtlam_pos : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hlh_pos : (0:ℝ) < Real.rpow lam (-((1:ℝ)/2)) := by rw [hlh]; positivity
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- n=1: log n = 0 ⇒ bracket = 0
    have hmaxeq : max n₁ n₂ = 1 := by have := le_max_left n₁ n₂; omega
    have hnval : n = 1 := by rw [hn_def, hmaxeq]; norm_num
    have hLval : L = 0 := by rw [hL_def, hnval]; simp
    rw [hLval]
    have hrhs0 : (0:ℝ) ≤ (Cbern * (Cfro + Centry) * Cinner) * Real.rpow lam (-1) := by
      have : (0:ℝ) < Real.rpow lam (-1) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
      positivity
    simp only [zero_div, Real.sqrt_zero, zero_mul, zero_add, mul_zero]
    linarith [hrhs0]
  · -- main case
    have hn2le : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hbig
    have hnpos : (0:ℝ) < n := by linarith
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    have hL1 : (1:ℝ) ≤ L := by rw [hL_def]; exact one_le_beta_log β n hβ hn2le hlogpos
    have hLpos : (0:ℝ) < L := by linarith
    set D : ℝ := Real.rpow x ((4:ℝ)/3) with hD_def
    have hcombine : Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) = D := by
      rw [hD_def, hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (le_of_lt hrR)]
    have hxleD : x ≤ D := by
      rw [hD_def, rpow_eq]
      calc x = x ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hDpos : (0:ℝ) < D := by linarith
    have hsample' : (m:ℝ) ≥ lam * D * n * L := by
      have heq : lam * D * n * L
          = lam * Real.rpow μ₀ ((4:ℝ)/3) * n * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log n) := by
        rw [← hcombine, hL_def]; ring
      rw [heq, ← hn_def] at *; exact hsample
    have hlbpos : (0:ℝ) < lam * D * n * L := by positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    have hn1n2 : (n₁:ℝ) * (n₂:ℝ) ≤ n^2 := by
      have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
      have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
      nlinarith [hn₁R, hn₂R]
    set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
    have hppos : (0:ℝ) < p := by rw [hp_def]; positivity
    have hLp_eq : L / p = L * ((n₁:ℝ) * (n₂:ℝ)) / m := by rw [hp_def]; field_simp
    -- KEY: (L/p) ≤ n/(lam*D)
    have hLp_le : L / p ≤ n / (lam * D) := by
      rw [hLp_eq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsample', hn1n2, hLpos, hDpos, hlam0, hnpos, hn₁R, hn₂R,
        mul_pos hlam0 hDpos, mul_pos hLpos (mul_pos hlam0 hDpos)]
    -- KEY2: (L/p)*(x/n) ≤ 1/lam
    have hkey : (L / p) * (x / n) ≤ 1 / lam := by
      calc (L / p) * (x / n) ≤ (n / (lam * D)) * (x / n) :=
            mul_le_mul_of_nonneg_right hLp_le (by positivity)
        _ = x / (lam * D) := by field_simp
        _ ≤ x / (lam * x) := by
            apply div_le_div_of_nonneg_left (le_of_lt hxpos) (by positivity)
            nlinarith [hxleD, hlam, hlam0, hxpos]
        _ = 1 / lam := by rw [mul_comm lam x, ← div_div, div_self (ne_of_gt hxpos)]
    have hLp_pos : (0:ℝ) < L / p := by positivity
    -- ===== TERM 1: √(L/p)*√(μ₀ r/n) ≤ lam^(-1/2) =====
    -- √(μ₀ r/n) = √(x/n)
    have hμrn : μ₀ * ((r:ℝ)/n) = x / n := by rw [hx_def]; ring
    have hT1 : Real.sqrt (L/p) * Real.sqrt (μ₀ * ((r:ℝ)/n)) ≤ Real.rpow lam (-((1:ℝ)/2)) := by
      rw [hμrn, ← Real.sqrt_mul (le_of_lt hLp_pos), hlh]
      have hrhs : (1:ℝ)/Real.sqrt lam = Real.sqrt (1/lam) := by
        rw [one_div, one_div, ← Real.sqrt_inv]
      rw [hrhs]
      exact Real.sqrt_le_sqrt hkey
    -- ===== TERM 2: (L/p)*(μ₀ r/n) ≤ lam^(-1/2) =====
    have hT2 : (L/p) * (μ₀ * ((r:ℝ)/n)) ≤ Real.rpow lam (-((1:ℝ)/2)) := by
      rw [hμrn, hlh]
      -- (L/p)(x/n) ≤ 1/lam ≤ 1/√lam
      calc (L/p) * (x/n) ≤ 1/lam := hkey
        _ ≤ 1/Real.sqrt lam := by
            apply div_le_div_of_nonneg_left (by norm_num) hsqrtlam_pos
            calc Real.sqrt lam ≤ Real.sqrt (lam*lam) := by
                  apply Real.sqrt_le_sqrt; nlinarith [hlam, hlam0]
              _ = lam := by rw [Real.sqrt_mul_self (le_of_lt hlam0)]
    -- ===== ASSEMBLE =====
    -- LHS = Cbern*(√(L/p)*(Cfro*(Cinner*λ^{-1/2})*√(μ₀r/n)) + (L/p)*(Centry*(Cinner*λ^{-1/2})*μ₀*(r/n)))
    -- Term1_full = Cinner*λ^{-1/2}*Cfro*(√(L/p)*√(μ₀r/n)) ≤ Cinner*λ^{-1/2}*Cfro*λ^{-1/2}
    have hci_lh_nn : (0:ℝ) ≤ Cinner * Real.rpow lam (-((1:ℝ)/2)) := by positivity
    have hT1full :
        Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
          Real.sqrt (μ₀ * ((r:ℝ)/n)))
          ≤ Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) := by
      rw [show Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
            Real.sqrt (μ₀ * ((r:ℝ)/n)))
          = (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2)))) *
            (Real.sqrt (L/p) * Real.sqrt (μ₀ * ((r:ℝ)/n))) by ring]
      apply mul_le_mul_of_nonneg_left hT1 (by positivity)
    have hT2full :
        (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n))
          ≤ Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) := by
      rw [show (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n))
          = (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2)))) *
            ((L/p) * (μ₀ * ((r:ℝ)/n))) by ring]
      apply mul_le_mul_of_nonneg_left hT2 (by positivity)
    -- λ^{-1/2}·λ^{-1/2} = λ^{-1}
    have hlh2 : Real.rpow lam (-((1:ℝ)/2)) * Real.rpow lam (-((1:ℝ)/2)) = Real.rpow lam (-1) :=
      (rpow_neg_one_split lam hlam0).symm
    calc Cbern *
            (Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
              Real.sqrt (μ₀ * ((r:ℝ)/n))) +
            (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n)))
        ≤ Cbern * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) +
            Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2))) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hT1full hT2full) (le_of_lt hCbern)
      _ = (Cbern * (Cfro + Centry) * Cinner) * Real.rpow lam (-1) := by
          rw [← hlh2]; ring
end MiddleDependency11
export MiddleDependency11 (inner_scaled_scalar_bernstein_lambda_scale_absorption)

-- Accepted proof by tianyipeng; submission d7bd8a03-9be5-4835-9a0e-ee16b9b6bce4.
-- Original source SHA-256: cd2da6cb8246b7f004c30f404dbe6623be7ccd30d7d5237e3fd312c019c28001.
namespace MiddleDependency12
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
end MiddleDependency12
export MiddleDependency12 (bernoulli_event_probability_mono)

-- Accepted proof by Shuze Chen; submission c6296928-627d-4adf-a53d-976bd703a8a0.
-- Original source SHA-256: 685b7961fff6c5c4d9523a52b51ed00f53b117d410e5daa84d63cbb6df6af5a5.
namespace MiddleDependency13
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
end MiddleDependency13
export MiddleDependency13 (sample_ratio_between_zero_and_one)

-- Accepted proof by tianyipeng; submission 90adc9be-985a-4a65-ac00-aab2d6cbbac1.
-- Original source SHA-256: 97a6e894149d8e1177b2d2230cc1b788c12f6035af41066acaaad4b9b05752da.
namespace MiddleDependency14
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
end MiddleDependency14
export MiddleDependency14 (bernoulli_event_intersection_probability_from_lower_bounds)

-- Accepted proof by Shuze Chen; submission d96236fe-dc5a-4196-ace2-62a6cfe0985e.
-- Original source SHA-256: a2ffdfc84af425cab3f9bb6480a9237433dcae46efc63d20923ef86ace6ae426.
namespace MiddleDependency15
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
end MiddleDependency15
export MiddleDependency15 (bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor)

-- Accepted proof by Shuze Chen; submission de149105-2e0c-4158-b24e-8fffcdaf8ffa.
-- Original source SHA-256: eaa875926d4cfc459931c518e80dbf88b3bb7fe3042af387510bb4a0e445fb56.
namespace MiddleDependency16
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
end MiddleDependency16
export MiddleDependency16 (pair_coordinate_cardinality_loss_absorbed_by_beta_shift)

end MiddleProof

open MatrixCompletion MiddleProof

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


theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        ∀ Cinner : ℝ, 0 < Cinner →
        ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
              μ₀ * ((r : ℝ) / (↑(max n₁ n₂)))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  rcases inner_scaled_scalar_bernstein_lambda_scale_absorption
      (3 * Cbern) Centry Cfro (by positivity) hCentry hCfro with
    ⟨Cpoint, hCpoint, hAbsorb⟩
  refine ⟨Cpoint, cbern, hCpoint, hcbern, ?_⟩
  intro beta lam hbeta hlam n1 n2 r m M mu0 mu1 S
    hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample Cinner hCinner Omega3 hInner
    hrepr hentry hfrob
  let p : ℝ := (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))
  let N : ℝ := (max n1 n2 : ℕ)
  let e : ℝ := Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
    mu0 * ((r : ℝ) / N)
  let f : ℝ := Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
    Real.sqrt (mu0 * ((r : ℝ) / N))
  have hp : 0 ≤ p ∧ p ≤ 1 := sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 1 ≤ max n1 n2 by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlam0 : 0 < lam := by linarith
  have hrpow : 0 < Real.rpow lam (-((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hlam0 _
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hscale :
      Cbern * (Real.sqrt (((beta + 4) * Real.log N) / p) * f +
        (((beta + 4) * Real.log N) / p) * e) ≤
      (Cpoint * Cinner) * Real.rpow lam (-1) := by
    apply le_trans (shifted_bernstein_scale Cbern e f beta (Real.log N) p
      hCbern.le he hf hbeta hlog hp.1)
    exact hAbsorb beta lam hbeta hlam n1 n2 r m mu0 Cinner
      hn1 hn2 hr hm hmu0 hCinner hsample
  have hpoint : ∀ w1 w2 : Fin n1 × Fin n2,
      bernoulliEventProb p
          (fun Omega2 => |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
            Cpoint * (Cinner * Real.rpow lam (-1))) ≥
        1 - cbern * Real.rpow N (-(beta + 4)) := by
    intro w1 _w2
    have hraw := hBernstein (beta + 4) (by linarith) n1 n2 m hn1 hn2 hm
      (fun Omega2 => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
      (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) e f
      (fun Omega2 => hrepr Omega2 w1) (hentry w1) (hfrob w1)
    apply le_trans hraw
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega2 hOmega2
    simpa [mul_assoc] using hOmega2.trans hscale
  have hUniform :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      Cpoint cbern hCpoint hcbern p (Cinner * Real.rpow lam (-1))
      (Real.rpow N (-(beta + 4))) hp.1 hp.2 n1 n2
      (fun w1 _w2 Omega2 => quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
      hpoint
  have hcard := pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    beta cbern n1 n2 hbeta hcbern hn1 hn2
  have hMono :
      bernoulliEventProb p
          (fun Omega2 => ∀ w1 w2 : Fin n1 × Fin n2,
            |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
              Cpoint * (Cinner * Real.rpow lam (-1))) ≤
      bernoulliEventProb p
          (fun Omega2 => QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
            ((Cpoint * Cinner) * Real.rpow lam (-1))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega2 hOmega2 w1
    simpa [mul_assoc] using hOmega2 w1 w1
  refine le_trans (le_trans ?_ hUniform) hMono
  dsimp [N] at *
  linarith

#print axioms solution
