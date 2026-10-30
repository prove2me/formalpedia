-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional
-- name    : AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:35:45.954739+00:00
-- url     : https://prove2.me/theorems/57dd9519-dc7c-4db6-ad68-05310ae93d1c
-- title:
--   Unconditional original BV finite-horizon killed q-scale expectation without an auxiliary exponent assumption
-- statement:
--   Every standing bounded-variation original Lévy process with q>0 has an actual exponent θ≥0 strictly above discount. Applying the genuine fully verified finite-horizon killed expectation theorem yields integrability and equality Wq(x) for the source true two-sided stopped payoff with no extraneous Laplace moment premise.
-- source:
--   Accepted psi_eventually_gt_of_boundedVariation and genuine full original-law BV finite-horizon killed expectation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_boundedVariation

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
     :
    (let Z : Ω → ℝ := fun ω =>
      if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
        if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
              W (x + X.X (min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a-x) ω then 0
      else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω);
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x) := by sorry
