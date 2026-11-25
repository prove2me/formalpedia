-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_eval_map
-- name    : Formalism.InvariantFactorPaths.INST.cor_eval_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:00:01.002802+00:00
-- url     : https://prove2.me/theorems/864f6430-95d7-40fc-a7a1-a89b42b5901d
-- title:
--   INST: cor eval map
-- statement:
--   The INST construction uses the cor eval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L156-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L156-L163

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.InvariantFactorPaths.INST.cor_eval_map (f0 : MvPolynomial (Fin r × Fin n) ℤ_[p]) :
    eval (idPoint ℚ_[p] r n) (map (algebraMap ℤ_[p] ℚ_[p]) f0) =
      algebraMap ℤ_[p] ℚ_[p] (eval (idPoint ℤ_[p] r n) f0) := by sorry
