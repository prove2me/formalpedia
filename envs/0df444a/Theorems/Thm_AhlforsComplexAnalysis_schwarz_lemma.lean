-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_schwarz_lemma
-- name    : AhlforsComplexAnalysis.schwarz_lemma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T04:46:55.309674+00:00
-- url     : https://prove2.me/theorems/a1f105fd-d557-45a9-9dd4-ba97c07f5fc0
-- title:
--   Schwarz's lemma
-- statement:
--   Let $f$ be analytic in the open unit disk $|z|<1$ with $|f(z)|\le 1$ there and $f(0)=0$. Then $|f(z)|\le|z|$ for all $|z|<1$ and $|f'(0)|\le 1$. If $|f(z)|=|z|$ for some $z\neq 0$ in the disk, or if $|f'(0)|=1$, then $f(z)=cz$ on the disk for a constant $c$ with $|c|=1$.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 4 §3.4, Theorem 13 (p. 135)

import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.schwarz_lemma {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1) (h0 : f 0 = 0) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧ ‖deriv f 0‖ ≤ 1 ∧
    (((∃ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) ∨ ‖deriv f 0‖ = 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = c * z) := by sorry
