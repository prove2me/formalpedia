-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_iff
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:46.879653+00:00
-- url     : https://prove2.me/theorems/6f1dd822-9030-4d17-b366-a7041765a2a1
-- title:
--   Valuation Nonnegativity: valuation nonneg iff
-- statement:
--   The Valuation Nonnegativity construction uses the valuation nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L14-L16

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

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_iff {a : C} : V.Ge 0 a ↔ 0 ≤ V.v a := by sorry
