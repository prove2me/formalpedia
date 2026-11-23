-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_zero_left
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:08.327803+00:00
-- url     : https://prove2.me/theorems/8609ba56-45d5-4b47-974c-a14f579925e7
-- title:
--   Is Bichar: map zero left
-- statement:
--   The Is Bichar construction uses the map zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L18-L21

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
variable {c : B → A → k}

theorem Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_zero_left (hc : IsBichar c) (a : A) : c 0 a = 1 := by sorry
