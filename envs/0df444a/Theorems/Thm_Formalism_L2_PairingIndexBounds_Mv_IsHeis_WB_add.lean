-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WB_add
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsHeis.WB_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:44.15952+00:00
-- url     : https://prove2.me/theorems/6dd6e23a-0cab-4d92-ad04-92e0359c09bc
-- title:
--   Is Heis: WB add
-- statement:
--   The Is Heis construction uses the WB add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L162-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L162-L163

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

theorem Formalism.L2.PairingIndexBounds.Mv.IsHeis.WB_add (hW : IsHeis c WA WB) (b b' : B) (x : T) : WB (b + b') x = WB b (WB b' x) := by sorry
