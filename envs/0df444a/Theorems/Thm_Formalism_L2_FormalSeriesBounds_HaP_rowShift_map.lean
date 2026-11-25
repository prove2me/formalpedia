-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_rowShift_map
-- name    : Formalism.L2.FormalSeriesBounds.HaP.rowShift_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:21.81083+00:00
-- url     : https://prove2.me/theorems/94e51862-7846-441a-9f7c-0e1e9300ff98
-- title:
--   Ha P: row Shift map
-- statement:
--   The Ha P construction uses the row Shift map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L49-L56

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)

theorem Formalism.L2.FormalSeriesBounds.HaP.rowShift_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (σ0 : Ty) (i i' : Fin (r σ0)) (t : k)
    (p : MvPolynomial (Letter Ty r n) k) :
    rowShift r n k' σ0 i i' (φ t) (map φ p) = map φ (rowShift r n k σ0 i i' t p) := by sorry
