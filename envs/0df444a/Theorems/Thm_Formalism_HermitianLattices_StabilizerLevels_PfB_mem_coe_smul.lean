-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_mem_coe_smul
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.mem_coe_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:26.262482+00:00
-- url     : https://prove2.me/theorems/0b990229-a9cb-4286-963f-4e0222989f64
-- title:
--   Pf B: mem coe smul
-- statement:
--   The Pf B construction uses the mem coe smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L723-L736
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L723-L736

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
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

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.mem_coe_smul (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) (z : E) :
    z ∈ (I : FractionalIdeal (𝓞 E)⁰ E) ↔
      σ z ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by sorry
