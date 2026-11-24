-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eq_of_out_sub_mem
-- name    : Formalism.L2.PairingIndexBounds.Mv.eq_of_out_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:09.647568+00:00
-- url     : https://prove2.me/theorems/4b9584e1-aed3-4f51-8b3e-f3a999b71a85
-- title:
--   Mv: eq of out sub mem
-- statement:
--   The Mv construction uses the eq of out sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L213-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L213-L218

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

theorem Formalism.L2.PairingIndexBounds.Mv.eq_of_out_sub_mem (A₀ : AddSubgroup A) (q q' : A ⧸ A₀) (h : q.out - q'.out ∈ A₀) : q = q' := by sorry
