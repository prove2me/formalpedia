-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_delta_le
-- name    : Formalism.InvariantFactorPaths.INST.cor_delta_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:00:48.452007+00:00
-- url     : https://prove2.me/theorems/437fe190-75e4-4a83-b9a5-c7dd8c0b83b9
-- title:
--   INST: cor delta le
-- statement:
--   The INST construction uses the cor delta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L177-L183

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

theorem Formalism.InvariantFactorPaths.INST.cor_delta_le (hk : RowGlDiv) (hI : SwpInt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (la : Fin r → ℤ) :
    DeltaLat p (GR p r ν) {h | (GR p r ν).IsHW la h ∧ h ∈ swappedDualWeyl p r n ν ∧
      h ∈ (IntPol p (Fin n × Fin r)).toAddSubgroup} ≤ (cor_L p hn ν).toAddSubgroup := by sorry
