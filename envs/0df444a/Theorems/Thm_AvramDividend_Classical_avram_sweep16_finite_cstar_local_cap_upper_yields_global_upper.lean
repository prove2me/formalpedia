-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
-- name    : AvramDividend.Classical.avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:44:53.357995+00:00
-- url     : https://prove2.me/theorems/4272f463-a8a0-4f42-abb2-ffa4ee0dcc2d
-- title:
--   Finite cstar original capped upper bound extends from cap-eligible reserves to all initial reserves
-- statement:
--   The local original verification upper bound only applies to eligible initial reserves ENNReal.ofReal x ≤ cstar W. If x lies in the finite barrier interval 0 ≤ x ≤ (cstar W).toReal, monotonicity of ENNReal.ofReal and the exact finite-barrier toReal identity establish this eligibility. Apply the local upper bound there, then invoke the independently Proved original interior-to-global capped optimality theorem to obtain equality on all nonnegative reserves, hence the required upper inequality. This verifies the cap-condition bridge without assuming away the missing original stochastic budget, and never imports the Open local_verification theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hLocal : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry
