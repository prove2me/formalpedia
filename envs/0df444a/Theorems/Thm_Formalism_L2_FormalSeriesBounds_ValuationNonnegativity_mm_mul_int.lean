-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_mul_int
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_mul_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:29.049029+00:00
-- url     : https://prove2.me/theorems/a6c93ff4-1269-46b0-9cb6-7ab57ec38824
-- title:
--   Valuation Nonnegativity: mm mul int
-- statement:
--   The Valuation Nonnegativity construction uses the mm mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L42-L46

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_mul_int {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by sorry
