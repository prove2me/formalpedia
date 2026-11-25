-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_sub
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:45:49.411776+00:00
-- url     : https://prove2.me/theorems/15a5c27e-8629-5cb9-8919-85e37b91d039
-- title:
--   Valuation Nonnegativity: mm sub
-- statement:
--   The Valuation Nonnegativity construction uses the mm sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L35-L37

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

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by sorry
