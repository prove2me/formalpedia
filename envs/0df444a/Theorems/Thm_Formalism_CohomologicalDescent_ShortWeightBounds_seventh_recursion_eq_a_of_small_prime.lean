-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_seventh_recursion_eq_a_of_small_prime
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.seventh_recursion_eq_a_of_small_prime
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:50.586361+00:00
-- url     : https://prove2.me/theorems/a187a863-371c-4f64-96a8-c838b5d7cb37
-- title:
--   Short Weight Bounds: seventh recursion eq a of small prime
-- statement:
--   The Short Weight Bounds construction uses the seventh recursion eq a of small prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L683-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L683-L685

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

theorem Formalism.CohomologicalDescent.ShortWeightBounds.seventh_recursion_eq_a_of_small_prime {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (l : ℕ)
    (hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) : W.Jrec7 P l = W.JA P l := by sorry
