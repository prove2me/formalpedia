-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoB_mem
-- name    : Formalism.L2.PairingIndexBounds.Mv.rhoB_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:55.7468+00:00
-- url     : https://prove2.me/theorems/e79a493b-1828-49c6-bdc2-cee035efb698
-- title:
--   Mv: rho B mem
-- statement:
--   The Mv construction uses the rho B mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L372-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L372-L383

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

theorem Formalism.L2.PairingIndexBounds.Mv.rhoB_mem (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) :
    ∀ Φ ∈ Sch c A₀, rhoB c b Φ ∈ Sch c A₀ := by sorry
