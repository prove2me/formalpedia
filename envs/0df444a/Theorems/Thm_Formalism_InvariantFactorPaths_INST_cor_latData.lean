-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_latData
-- name    : Formalism.InvariantFactorPaths.INST.cor_latData
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:00:51.494675+00:00
-- url     : https://prove2.me/theorems/de8508b5-34ce-4506-b7dc-2b7891920cdf
-- title:
--   INST: cor lat Data
-- statement:
--   The INST construction uses the cor lat Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L48-L65

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

theorem Formalism.InvariantFactorPaths.INST.cor_latData (h1 : RowGlOne) (hw : SwpWt) (hP : SwpPol) (ν : Fin n → ℕ) (l : ℕ)
    (hS : Spread ℚ_[p] r n ν l) :
    LatData p (GR p r ν) (swappedDualWeyl p r n ν) (IntPol p (Fin n × Fin r)).toAddSubgroup l := by sorry
