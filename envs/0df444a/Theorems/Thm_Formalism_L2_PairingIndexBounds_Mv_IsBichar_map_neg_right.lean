-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_neg_right
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_neg_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:47.667417+00:00
-- url     : https://prove2.me/theorems/544a4142-6daa-407a-aff5-3c840723763e
-- title:
--   Is Bichar: map neg right
-- statement:
--   The Is Bichar construction uses the map neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L23-L25

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

theorem Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_neg_right (hc : IsBichar c) (b : B) (a : A) : c b (-a) = (c b a)⁻¹ := by sorry
