-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_eq_eFam
-- name    : Formalism.L2.PairingIndexBounds.Mv.gen_eq_eFam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:44.064517+00:00
-- url     : https://prove2.me/theorems/e5e9c44a-f7fe-4444-968a-6eba0239eac1
-- title:
--   Mv: gen eq e Fam
-- statement:
--   The Mv construction uses the gen eq e Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L256-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L256-L278

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

theorem Formalism.L2.PairingIndexBounds.Mv.gen_eq_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (a : A) (b : B) :
    gen c A₀ a b = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by sorry
