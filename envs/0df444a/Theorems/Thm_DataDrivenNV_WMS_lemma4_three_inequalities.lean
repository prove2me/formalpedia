-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_lemma4_three_inequalities
-- name    : DataDrivenNV.WMS.lemma4_three_inequalities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:15.419688+00:00
-- url     : https://prove2.me/theorems/761b2f84-4911-44ff-8bb2-2bb8334b79c3
-- title:
--   Lemma 4, p. 15 — three elementary inequalities for β ∈ (0,1), η ∈ (−1/(1−β), 1/β)
-- statement:
--   Let $\beta\in(0,1)$ and $\eta\in\big(-\frac1{1-\beta},\frac1\beta\big)$. Then
--
--   1. $$\Big(\frac1{1-\beta}+\eta\Big)\log\big(1+\eta(1-\beta)\big)+\Big(\frac1\beta-\eta\Big)\log(1-\eta\beta)-\min\{\beta,1-\beta\}\,\eta^2\ \ge\ 0,$$
--   2. $$\frac{\beta}{1-\beta}\log\frac1\beta-\beta\ \ge\ 0,$$
--   3. $$\frac{1-\beta}{\beta}\log\frac1{1-\beta}-(1-\beta)\ \ge\ 0.$$
--
--   With $\eta=\gamma_1/\gamma_0$ and $\beta=b/(b+h)$ these give $z^*_{q^*,\gamma_0,\gamma_1}\ge\frac1{\gamma_0}\frac{\min(b,h)}{b+h}$ in each of the three cases of the proof of Proposition 2.
--
--   **Formalization Note** Logarithms are natural logarithms. The last two inequalities do not involve $\eta$; they are kept in one statement as printed.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 15, Lemma 4; proof EC.6, pp. ec9–ec10

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Lemma 4** (p. 15): for `β ∈ (0,1)` and `η ∈ (−1/(1−β), 1/β)`, three elementary inequalities. -/
theorem lemma4_three_inequalities (β η : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη0 : -(1 / (1 - β)) < η) (hη1 : η < 1 / β) :
    0 ≤ (1 / (1 - β) + η) * Real.log (1 + η * (1 - β)) + (1 / β - η) * Real.log (1 - η * β)
        - min β (1 - β) * η ^ 2 ∧
    0 ≤ β / (1 - β) * Real.log (1 / β) - β ∧
    0 ≤ (1 - β) / β * Real.log (1 / (1 - β)) - (1 - β) := by sorry

end DataDrivenNV.WMS
