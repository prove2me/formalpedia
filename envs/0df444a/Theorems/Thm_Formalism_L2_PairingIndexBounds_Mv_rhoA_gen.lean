-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoA_gen
-- name    : Formalism.L2.PairingIndexBounds.Mv.rhoA_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:41.910251+00:00
-- url     : https://prove2.me/theorems/bec606a0-4fb2-4091-a2cd-7b5e65cdaafb
-- title:
--   Mv: rho A gen
-- statement:
--   The Mv construction uses the rho A gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L346-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L346-L350

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

theorem Formalism.L2.PairingIndexBounds.Mv.rhoA_gen (c : B → A → k) (A₀ : AddSubgroup A) (a' a : A) (b : B) :
    rhoA a' (gen c A₀ a b) = gen c A₀ (a' + a) b := by sorry
