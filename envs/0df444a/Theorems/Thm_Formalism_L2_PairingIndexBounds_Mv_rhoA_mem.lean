-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoA_mem
-- name    : Formalism.L2.PairingIndexBounds.Mv.rhoA_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:59.801015+00:00
-- url     : https://prove2.me/theorems/bf244db5-7532-45eb-b1bd-d36db01773f8
-- title:
--   Mv: rho A mem
-- statement:
--   The Mv construction uses the rho A mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L360-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L360-L370

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

theorem Formalism.L2.PairingIndexBounds.Mv.rhoA_mem (c : B → A → k) (A₀ : AddSubgroup A) (a : A) : ∀ Φ ∈ Sch c A₀, rhoA a Φ ∈ Sch c A₀ := by sorry
