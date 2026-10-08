-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_eq_15
-- name    : AddLogReg.ExpCrit.eq_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:03:54.684837+00:00
-- url     : https://prove2.me/theorems/d6528d02-baf1-4f22-a7fd-aca49e27af0d
-- title:
--   (15), p. 346 — e^{F}/(e^{−F} + e^{F}) = e^{2F}/(1 + e^{2F}): the symmetric and usual logistic transforms differ by a factor 2
-- statement:
--   For every real number $F$,
--   $$\frac{e^{F}}{e^{-F} + e^{F}} = \frac{e^{2F}}{1 + e^{2F}}.$$
--
--   The left-hand side is the symmetric logistic transform appearing in (13); the right-hand side is the usual logistic model (15) evaluated at $2F$. Hence the model of Lemma 1 and the usual logistic model are equivalent up to a factor $2$ in $F$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 346, (15)

import Mathlib

namespace AddLogReg.ExpCrit

/-- Display (15) (p. 346): multiplying numerator and denominator of (13) by `e^{F}` gives the
usual logistic model, `e^{F}/(e^{−F} + e^{F}) = e^{2F}/(1 + e^{2F})`. -/
theorem eq_15 (F : ℝ) :
    Real.exp F / (Real.exp (-F) + Real.exp F) = Real.exp (2 * F) / (1 + Real.exp (2 * F)) := by sorry

end AddLogReg.ExpCrit
