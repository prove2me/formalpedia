-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_of_not_mem
-- name    : Formalism.L2.PairingIndexBounds.Mv.eFam_of_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:44.184799+00:00
-- url     : https://prove2.me/theorems/e06342ed-daaa-474b-a520-e6de9eb21cd8
-- title:
--   Mv: e Fam of not mem
-- statement:
--   The Mv construction uses the e Fam of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L202-L204

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

theorem Formalism.L2.PairingIndexBounds.Mv.eFam_of_not_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∉ A₀) :
    eFam A₀ i t = 0 := by sorry
