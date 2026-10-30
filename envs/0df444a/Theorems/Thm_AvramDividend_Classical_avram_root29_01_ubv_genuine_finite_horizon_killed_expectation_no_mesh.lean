-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
-- name    : AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:19:23.226021+00:00
-- url     : https://prove2.me/theorems/a593c037-8461-46aa-8bf6-f77587de59bf
-- title:
--   Original UBV finite-horizon continuously killed q-scale expectation without mesh parameters
-- statement:
--   For every genuine unbounded-variation source Levy process and q>0, positive upper cap and initial capital x in [0,a], the actual finite-horizon lower-history-killed upper/lower first-passage reward has original-P expectation W(x), independently of any artificial approximation mesh; include the origin and cap ties.
-- source:
--   Proved UBV mesh-parametric unconditional killed expectation and canonical positive dyadic mesh existence.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation_no_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
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
