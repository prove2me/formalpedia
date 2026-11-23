-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_chi_apply
-- name    : Formalism.L2.PairingIndexBounds.Mv.chi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:22.475324+00:00
-- url     : https://prove2.me/theorems/392c227a-da47-4700-a42e-b4eafa92707e
-- title:
--   Mv: chi apply
-- statement:
--   The Mv construction uses the chi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L192-L193

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

theorem Formalism.L2.PairingIndexBounds.Mv.chi_apply (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) (s : A₀) :
    chi c hc A₀ b (Multiplicative.ofAdd s) = c b (s : A) := by sorry
