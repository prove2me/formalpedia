-- Prove2me | Theorems.Thm_Aggmetrics_skew_invariant_iff_factors_through_recall_specificity
-- name    : Aggmetrics.skew_invariant_iff_factors_through_recall_specificity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:34.063241+00:00
-- url     : https://prove2.me/theorems/23c404eb-b2a7-4f7f-9b7c-b8f55575aca3
-- title:
--   Aggmetrics: skew invariant iff factors through recall specificity
-- statement:
--   **Skew-invariance characterisation.**
--
--   A binary measure `M`, defined for all positive-margin cells `(tp, fp, fn, tn)`
--   (`tp + fn > 0`, `fp + tn > 0`), is *skew-invariant* — invariant to independently
--   rescaling the positive-class counts `(tp, fn)` by any `λ > 0` and the negative-class
--   counts `(fp, tn)` by any `μ > 0` — if and only if `M` factors through recall and
--   specificity alone: there exists `g : ℝ → ℝ → ℝ` with
--   `M tp fp fn tn = g (tp / (tp + fn)) (tn / (fp + tn))` everywhere on the domain.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L72-L103
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L72-L103

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.skew_invariant_iff_factors_through_recall_specificity
    (M : ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      ∀ lam mu : ℝ, 0 < lam → 0 < mu →
        M (lam * tp) (mu * fp) (lam * fn) (mu * tn) = M tp fp fn tn)
    ↔
    (∃ g : ℝ → ℝ → ℝ, ∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      M tp fp fn tn = g (tp / (tp + fn)) (tn / (fp + tn))) := by sorry
