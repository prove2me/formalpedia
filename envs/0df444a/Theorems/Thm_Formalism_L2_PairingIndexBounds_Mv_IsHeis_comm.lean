-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_comm
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsHeis.comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:08.019439+00:00
-- url     : https://prove2.me/theorems/a6d05702-a544-4ebb-9927-5fbe235b5694
-- title:
--   Is Heis: comm
-- statement:
--   The Is Heis construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L165-L166

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
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}

theorem Formalism.L2.PairingIndexBounds.Mv.IsHeis.comm (hW : IsHeis c WA WB) (a : A) (b : B) (x : T) : WA a (WB b x) = c b a • WB b (WA a x) := by sorry
