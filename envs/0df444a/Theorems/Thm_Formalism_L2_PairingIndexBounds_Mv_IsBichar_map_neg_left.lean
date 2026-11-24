-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_neg_left
-- name    : Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_neg_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:10.310803+00:00
-- url     : https://prove2.me/theorems/287179bc-1b53-47ae-b7eb-9d16efbe4f6e
-- title:
--   Is Bichar: map neg left
-- statement:
--   The Is Bichar construction uses the map neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L27-L29

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

theorem Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_neg_left (hc : IsBichar c) (b : B) (a : A) : c (-b) a = (c b a)⁻¹ := by sorry
