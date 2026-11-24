-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Sch_le_span_eFam
-- name    : Formalism.L2.PairingIndexBounds.Mv.Sch_le_span_eFam
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:09.80306+00:00
-- url     : https://prove2.me/theorems/7f51dfc9-2862-4524-9571-fbc1193b257d
-- title:
--   Mv: Sch le span e Fam
-- statement:
--   The Mv construction uses the Sch le span e Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L308-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L308-L314

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

theorem Formalism.L2.PairingIndexBounds.Mv.Sch_le_span_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) :
    Sch c A₀ ≤ Submodule.span k (Set.range (eFam (k := k) A₀)) := by sorry
