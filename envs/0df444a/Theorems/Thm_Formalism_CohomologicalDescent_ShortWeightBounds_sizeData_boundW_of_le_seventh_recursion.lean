-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_sizeData_boundW_of_le_seventh_recursion
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.sizeData_boundW_of_le_seventh_recursion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:20.944912+00:00
-- url     : https://prove2.me/theorems/68ddd270-3dbd-56d5-b74d-2afbf4337c1f
-- title:
--   Short Weight Bounds: size Data bound W of le seventh recursion
-- statement:
--   The Short Weight Bounds construction uses the size Data bound W of le seventh recursion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L691-L706
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L691-L706

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

theorem Formalism.CohomologicalDescent.ShortWeightBounds.sizeData_boundW_of_le_seventh_recursion {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (hH : P.Hyp)
    (hL : P.Large) (hW : W.Ok P) (J : ℕ → ℕ) (hJ : ∀ l : ℕ, l.Prime → J l ≤ W.Jrec7 P l) :
    (W.sizeData₂ P J).BoundW P := by sorry
