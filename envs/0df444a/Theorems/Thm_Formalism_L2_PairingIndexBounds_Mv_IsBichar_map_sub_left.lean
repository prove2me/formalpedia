-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_sub_left
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:13.494055+00:00
-- url     : https://prove2.me/theorems/b49285a4-2a80-4339-b394-508d7d251c3d
-- title:
--   Is Bichar: map sub left
-- statement:
--   The Is Bichar construction uses the map sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L34-L35

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

theorem Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_left (hc : IsBichar c) (b b' : B) (a : A) : c (b - b') a = c b a * (c b' a)⁻¹ := by sorry
