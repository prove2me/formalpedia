-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_W_le_iso
-- name    : Formalism.InvariantFactorPaths.INST.cor_W_le_iso
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:16.894503+00:00
-- url     : https://prove2.me/theorems/d5352c67-6743-55d8-9fb0-bddb8f8418c0
-- title:
--   INST: cor W le iso
-- statement:
--   The INST construction uses the cor W le iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L111-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L111-L125

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

theorem Formalism.InvariantFactorPaths.INST.cor_W_le_iso (h1 : RowGlOne) (hk : RowGlDiv) (hw' : SwpWt) (hP : SwpPol) (hn : n ≤ r) (ν : Fin n → ℕ)
    (hν : Antitone ν) :
    swappedDualWeyl p r n ν ≤ IsoW (GR p r ν) (swappedDualWeyl p r n ν) (fun a => (rowNu ν a : ℤ)) := by sorry
