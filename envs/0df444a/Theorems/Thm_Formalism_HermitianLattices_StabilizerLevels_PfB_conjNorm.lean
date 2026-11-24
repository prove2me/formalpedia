-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_conjNorm
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.conjNorm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:11.63256+00:00
-- url     : https://prove2.me/theorems/003de350-eada-4e5c-b6c4-a570e512f8f3
-- title:
--   Pf B: conj Norm
-- statement:
--   The Pf B construction uses the conj Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L776-L860
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L776-L860

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.conjNorm (K : IntermediateField ℚ E) (hK : Module.finrank ℚ K = 2) (σ : E ≃ₐ[ℚ] E) (β : K)
    (hβ : σ (β : E) ≠ β) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥) :
    𝔠.map (algebraMap (𝓞 K) (𝓞 E)) * σ • (𝔠.map (algebraMap (𝓞 K) (𝓞 E))) =
      Ideal.span {((Ideal.absNorm 𝔠 : ℕ) : 𝓞 E)} := by sorry
