-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Sch_ext
-- name    : Formalism.L2.PairingIndexBounds.Mv.Sch_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:41.771158+00:00
-- url     : https://prove2.me/theorems/c529f74a-6c11-46cc-accc-c10bec5b388e
-- title:
--   Mv: Sch ext
-- statement:
--   The Mv construction uses the Sch ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L170-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L170-L185

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

theorem Formalism.L2.PairingIndexBounds.Mv.Sch_ext {c : B → A → k} {A₀ : AddSubgroup A} {f g : Sch c A₀ →ₗ[k] T}
    (h : ∀ a b, f ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = g ⟨gen c A₀ a b, gen_mem c A₀ a b⟩) : f = g := by sorry
