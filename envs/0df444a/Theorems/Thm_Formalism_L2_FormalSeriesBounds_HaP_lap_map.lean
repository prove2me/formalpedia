-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_lap_map
-- name    : Formalism.L2.FormalSeriesBounds.HaP.lap_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:36.55133+00:00
-- url     : https://prove2.me/theorems/871185e8-2cd1-4ba5-9cf1-17142b054fbc
-- title:
--   Ha P: lap map
-- statement:
--   The Ha P construction uses the lap map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L44-L47

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

theorem Formalism.L2.FormalSeriesBounds.HaP.lap_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (τ τ' : Ty) (a0 : Fin (r τ)) (a1 : Fin (r τ'))
    (p : MvPolynomial (Letter Ty r n) k) :
    lap r n k' 1 τ τ' a0 a1 (map φ p) = map φ (lap r n k 1 τ τ' a0 a1 p) := by sorry
