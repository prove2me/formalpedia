-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
-- name    : AvramDividend.Classical.avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:27:08.514297+00:00
-- url     : https://prove2.me/theorems/2f23108e-57b1-4f1a-bd84-428a77997cb1
-- title:
--   Actual UBV strict upper-first stopped terminal real reward integrates to the q-scale
-- statement:
--   For a genuine non-standing unbounded-variation source spectrally negative Levy process and every positive q, 0<=x<=a, the original-P Bochner expectation of the strict upper-first discounted q-scale terminal payoff is W(x). Derive by dominated limit of true finite-horizon two-branch stopped killed rewards.
-- source:
--   Noncircular UBV finite-horizon two-branch balance plus Proved source-independent boundedness/nonnegativity/pointwise terminal limit and bounded real-integral convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (let F : Ω → ℝ := fun ω =>
      if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0;
    Integrable F P ∧ (∫ ω, F ω ∂P) = W x) := by sorry
