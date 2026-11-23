-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RowsOrigin_off_core
-- name    : Formalism.DivisionValues.RowsOrigin.off_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:18.668679+00:00
-- url     : https://prove2.me/theorems/9ca57083-a998-4da4-8b03-b2557919b732
-- title:
--   Rows Origin: off core
-- statement:
--   The Rows Origin construction uses the off core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L65-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L65-L103

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

theorem Formalism.DivisionValues.RowsOrigin.off_core {n wr T : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H3 : wr ≤ νr (Fin.last (n + 1))) (H4 : (νr 0 : ℝ) ≤ (wr : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by sorry
