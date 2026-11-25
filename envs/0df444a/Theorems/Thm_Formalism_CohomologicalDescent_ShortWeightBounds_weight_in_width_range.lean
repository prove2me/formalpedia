-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_in_width_range
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.weight_in_width_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:38.093999+00:00
-- url     : https://prove2.me/theorems/2d66d651-9fb8-5917-985f-994cc8ab6b69
-- title:
--   Short Weight Bounds: weight in width range
-- statement:
--   The Short Weight Bounds construction uses the weight in width range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L463-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L463-L470

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

theorem Formalism.CohomologicalDescent.ShortWeightBounds.weight_in_width_range {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) (a : ℕ) (ha : a < P.Nr) :
    W.U P τ (P.Nr - 1) ≤ UN P.Nr (W.lam τ) a ∧
      UN P.Nr (W.lam τ) a ≤ W.U P τ (P.Nr - 1) + ((W.width P τ).toNat : ℤ) := by sorry
