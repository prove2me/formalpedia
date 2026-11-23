-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_apply
-- name    : Formalism.L2.PairingIndexBounds.Mv.gen_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:57.5425+00:00
-- url     : https://prove2.me/theorems/de6a5b51-9499-4938-af6e-15b4a99475b6
-- title:
--   Mv: gen apply
-- statement:
--   The Mv construction uses the gen apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L45-L46

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

theorem Formalism.L2.PairingIndexBounds.Mv.gen_apply (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) (t : A) :
    gen c A₀ a b t = c b (t + a) * ind (A₀ : Set A) (t + a) := by sorry
