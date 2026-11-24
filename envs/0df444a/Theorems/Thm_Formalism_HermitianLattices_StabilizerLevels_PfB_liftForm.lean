-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_liftForm
-- name    : Formalism.HermitianLattices.StabilizerLevels.PfB.liftForm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:32.36254+00:00
-- url     : https://prove2.me/theorems/83f1933a-bb83-4a57-a509-81c9a7039878
-- title:
--   Pf B: lift Form
-- statement:
--   The Pf B construction uses the lift Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L346-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean#L346-L407

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
open NumberField IsDedekindDomain
open scoped TensorProduct

theorem Formalism.HermitianLattices.StabilizerLevels.PfB.liftForm {G : Type} [Group G] (Γ U : Subgroup G)
    (hst : ∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1)
    {W V : Type} [MulAction U W] [MulAction U V] (p : W → V)
    (hp : ∀ (u : U) (x : W), p (u • x) = u • p x) (f : G → V) (hf : IsForm Γ U f)
    (hs : ∀ g, ∃ x, p x = f g) : ∃ f' : G → W, IsForm Γ U f' ∧ ∀ g, p (f' g) = f g := by sorry
