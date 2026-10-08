-- Prove2me | Theorems.Thm_AvgLMS_Expect_lemma_3
-- name    : AvgLMS.Expect.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:31.574741+00:00
-- url     : https://prove2.me/theorems/1d380304-b770-46f0-a0a2-f19218264b16
-- title:
--   Lemma 3, p. 16 — for u ∈ [0, 1] and n > 0, (1 − (1 − u)ⁿ)² ≤ nu
-- statement:
--   For every real $u\in[0,1]$ and every integer $n>0$,
--   $$\big(1-(1-u)^n\big)^2\le n\,u .$$
--
--   This elementary inequality controls the bias term of Lemma 2: applied with $u=\gamma\lambda$ for each eigenvalue $\lambda$ of $H$, it shows $\langle\alpha_0,[I-(I-\gamma H)^n]^2(n\gamma H)^{-1}\alpha_0\rangle\le\|\alpha_0\|^2$.
--
--   **Formalization Note.** $n$ is a natural number, as in its use for the power $(I-\gamma H)^n$; for real $0<n<1$ and $u=1$ the inequality would fail.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, Lemma 3, App. A.6, p. 16

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Lemma 3, App. A.6, p. 16: for `u ∈ [0, 1]` and an integer `n > 0`, `(1 − (1 − u)ⁿ)² ≤ n u`. -/
theorem lemma_3 :
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ n : ℕ, 0 < n → (1 - (1 - u) ^ n) ^ 2 ≤ (n : ℝ) * u := by sorry
end AvgLMS.Expect
