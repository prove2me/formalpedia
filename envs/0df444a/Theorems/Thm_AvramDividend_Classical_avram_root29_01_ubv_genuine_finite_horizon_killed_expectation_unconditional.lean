-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_unconditional
-- name    : AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:08:38.834663+00:00
-- url     : https://prove2.me/theorems/035b56d6-2a56-4d15-9cba-2d96a57758fa
-- title:
--   Original UBV finite-horizon continuously killed q-scale expectation without auxiliary exponent premise
-- statement:
--   For every true unbounded-variation spectrally negative Levy process, q>0, nonnegative x<=a, finite horizon and positive vanishing ceiling-grid mesh, the explicitly killed scale reward has original-P expectation W(x) without requiring an auxiliary Laplace exponent margin. The margin follows from the Proved UBV eventual growth of the actual exponent.
-- source:
--   Proved UBV original finite-horizon killed expectation and actual exponent growth from unbounded variation.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
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
