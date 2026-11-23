-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RowsOrigin_top_core
-- name    : Formalism.DivisionValues.RowsOrigin.top_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:36.872809+00:00
-- url     : https://prove2.me/theorems/9fcc4507-99c0-4b47-a2af-9a324f30d80f
-- title:
--   Rows Origin: top core
-- statement:
--   The Rows Origin construction uses the top core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L116-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L116-L165

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

theorem Formalism.DivisionValues.RowsOrigin.top_core {n wr T aT : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H0 : νr 0 = aT + wr) (Hl : νr (Fin.last (n + 1)) ≤ wr)
    (H3 : wr + T ≤ ar (Fin.last n)) (H4 : (ar 0 : ℝ) ≤ (wr : ℝ) + (T : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by sorry
