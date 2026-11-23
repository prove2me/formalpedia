-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RowsOrigin_origin_rewrite
-- name    : Formalism.DivisionValues.RowsOrigin.origin_rewrite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:52.929008+00:00
-- url     : https://prove2.me/theorems/949738ee-f0ef-4b54-b958-0fdec2240d9e
-- title:
--   Rows Origin: origin rewrite
-- statement:
--   The Rows Origin construction uses the origin rewrite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L167-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L167-L183

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

theorem Formalism.DivisionValues.RowsOrigin.origin_rewrite {n j t w s wr : ℕ} {m : ℝ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (hj : 1 ≤ j) (hs : (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2)
    (hw : wr + s = w)
    (hν : ∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1))
    (ha : ∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) :
    (∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2)) ∧
    (∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) +
      (((j - 1) * t : ℕ) : ℝ)) := by sorry
