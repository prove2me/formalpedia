-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_swapped_highest_weight_isHW
-- name    : Formalism.InvariantFactorPaths.INST.swapped_highest_weight_isHW
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:00:41.549094+00:00
-- url     : https://prove2.me/theorems/bf7001c7-5bca-4942-b6b1-d78caa2bfb66
-- title:
--   INST: swapped highest weight is HW
-- statement:
--   The INST construction uses the swapped highest weight is HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L89-L94

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}

theorem Formalism.InvariantFactorPaths.INST.swapped_highest_weight_isHW (h1 : RowGlOne) (hw' : SwpWt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (GR p r ν).IsHW (fun a => (rowNu ν a : ℤ)) (swappedHighestWeight p hn ν) := by sorry
