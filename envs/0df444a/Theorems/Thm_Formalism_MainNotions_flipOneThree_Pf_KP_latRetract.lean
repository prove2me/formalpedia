-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_KP_latRetract
-- name    : Formalism.MainNotions.flipOneThree.Pf.KP.latRetract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:53.543869+00:00
-- url     : https://prove2.me/theorems/4437876a-38a8-4363-b396-7bd2e1759aed
-- title:
--   KP: lat Retract
-- statement:
--   The KP construction uses the lat Retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LatRetract.lean#L83-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LatRetract.lean#L83-L154

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LatRetract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
open Submodule
variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem Formalism.MainNotions.flipOneThree.Pf.KP.latRetract {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V'] {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V') (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) : ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧ ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b) := by sorry
