-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_swap_mem_swappedDualWeyl
-- name    : Formalism.InvariantFactorPaths.INST.swap_mem_swappedDualWeyl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:11.702649+00:00
-- url     : https://prove2.me/theorems/ba1e0412-9764-5c6f-99b1-9b4e3a3e2dc8
-- title:
--   INST: swap mem swapped Dual Weyl
-- statement:
--   The INST construction uses the swap mem swapped Dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean#L21-L22

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

theorem Formalism.InvariantFactorPaths.INST.swap_mem_swappedDualWeyl {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℚ_[p]} (hf : f ∈ dualWeyl ℚ_[p] r n ν) :
    swp ℚ_[p] r n f ∈ swappedDualWeyl p r n ν := by sorry
