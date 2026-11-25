-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_of_pow
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_of_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:29.716985+00:00
-- url     : https://prove2.me/theorems/b2c255c5-055e-4213-bc47-1b33db783426
-- title:
--   Valuation Nonnegativity: valuation nonneg of pow
-- statement:
--   The Valuation Nonnegativity construction uses the valuation nonneg of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L65-L73

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

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_of_pow {a : C} {n : ℕ} (h : V.Ge 0 (a ^ n)) (hn : n ≠ 0) : V.Ge 0 a := by sorry
