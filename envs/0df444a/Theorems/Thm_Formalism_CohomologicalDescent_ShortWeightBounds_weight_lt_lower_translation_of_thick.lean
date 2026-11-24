-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_lt_lower_translation_of_thick
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.weight_lt_lower_translation_of_thick
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:44.919184+00:00
-- url     : https://prove2.me/theorems/253d9c30-74af-4813-8519-4fa473608cac
-- title:
--   Short Weight Bounds: weight lt lower translation of thick
-- statement:
--   The Short Weight Bounds construction uses the weight lt lower translation of thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L187-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L187-L196

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

theorem Formalism.CohomologicalDescent.ShortWeightBounds.weight_lt_lower_translation_of_thick (P : Par) (hP : P.Hyp) (hL : P.Large) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι)
    (hτ : τ ∈ W.T2) (a : ℕ) (h1 : kc P ≤ a) (h2 : a < P.Nr) : W.U P τ a < W.xm τ := by sorry
