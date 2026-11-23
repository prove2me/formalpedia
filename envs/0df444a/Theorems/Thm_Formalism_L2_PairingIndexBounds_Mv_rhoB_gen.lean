-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoB_gen
-- name    : Formalism.L2.PairingIndexBounds.Mv.rhoB_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:37.063053+00:00
-- url     : https://prove2.me/theorems/85c64f6b-733a-4dee-acae-d6aadc08bed1
-- title:
--   Mv: rho B gen
-- statement:
--   The Mv construction uses the rho B gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L352-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L352-L358

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

theorem Formalism.L2.PairingIndexBounds.Mv.rhoB_gen (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b' : B) (a : A) (b : B) :
    rhoB c b' (gen c A₀ a b) = (c b' a)⁻¹ • gen c A₀ a (b' + b) := by sorry
