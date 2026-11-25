-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_exponent_mul_log_le_choose_mul_log
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.exponent_mul_log_le_choose_mul_log
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:45.654189+00:00
-- url     : https://prove2.me/theorems/fe22a434-0453-4db3-807d-03b1244d9347
-- title:
--   Short Weight Bounds: exponent mul log le choose mul log
-- statement:
--   The Short Weight Bounds construction uses the exponent mul log le choose mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L438-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L438-L461

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds

theorem Formalism.CohomologicalDescent.ShortWeightBounds.exponent_mul_log_le_choose_mul_log (N l w e : ℕ) (y : ℝ) (he : e ≤ N.choose 2 * Nat.log l w) (hy : (w : ℝ) ≤ y)
    (hy1 : 1 ≤ y) : (e : ℝ) * Real.log l ≤ (N.choose 2 : ℝ) * Real.log y := by sorry
