-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RowsOrigin_origin_interlace
-- name    : Formalism.DivisionValues.RowsOrigin.origin_interlace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:55.543408+00:00
-- url     : https://prove2.me/theorems/13d44827-4986-411c-9e14-dd2adb9ed300
-- title:
--   Rows Origin: origin interlace
-- statement:
--   The Rows Origin construction uses the origin interlace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L185-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L185-L208

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RowsOrigin

theorem Formalism.DivisionValues.RowsOrigin.origin_interlace {n wr T : ℕ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (eν : ∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2))
    (ea : ∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) + (T : ℝ))
    (hint : ∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) :
    (∀ i, ar i ≤ νr i.castSucc + T) ∧ (∀ i, νr i.succ + T ≤ ar i) := by sorry
