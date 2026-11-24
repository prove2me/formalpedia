-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_mem_div_smul
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.mem_div_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:21.956248+00:00
-- url     : https://prove2.me/theorems/46dce332-ca5d-4b3e-9aab-c242a79b0b2f
-- title:
--   Pf B: mem div smul
-- statement:
--   The Pf B construction uses the mem div smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L738-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L738-L754

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

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.mem_div_smul (σ : E ≃ₐ[ℚ] E) (I J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (hJ' : σ • J ≠ ⊥) (y : E) :
    y ∈ (I : FractionalIdeal (𝓞 E)⁰ E) * (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔
      σ y ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by sorry
