-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_sub_right
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:50.666613+00:00
-- url     : https://prove2.me/theorems/d9955872-f0c6-537f-9ed1-06cfc22f0701
-- title:
--   Is Bichar: map sub right
-- statement:
--   The Is Bichar construction uses the map sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L31-L32

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

theorem Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_right (hc : IsBichar c) (b : B) (a a' : A) : c b (a - a') = c b a * (c b a')⁻¹ := by sorry
