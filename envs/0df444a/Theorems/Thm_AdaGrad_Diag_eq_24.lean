-- Prove2me | Theorems.Thm_AdaGrad_Diag_eq_24
-- name    : AdaGrad.Diag.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:17:34.496313+00:00
-- url     : https://prove2.me/theorems/c8c1ff34-c667-4e3c-ab27-e7e7edb802ef
-- title:
--   (24) — the Auer–Gentile inequality Σₜ aₜ²/‖a_{1:t}‖₂ ≤ 2‖a_{1:T}‖₂
-- statement:
--   Let $a_1,a_2,\dots$ be any sequence of real numbers and write $a_{1:t}=(a_1,\dots,a_t)$, so that $\|a_{1:t}\|_2=\big(\sum_{\tau=1}^ta_\tau^2\big)^{1/2}$. Then for every $T$,
--   $$\sum_{t=1}^T\frac{a_t^2}{\|a_{1:t}\|_2}\le2\,\|a_{1:T}\|_2,$$
--   where $0/0=0$.
--
--   Applied coordinate by coordinate to the subgradients, this scalar inequality controls the gradient terms in the regret of AdaGrad.
--
--   **Formalization Note** Lean's division convention $x/0=0$ is the paper's $0/0=0$ (a zero denominator forces $a_t=0$). Rounds are 1-based.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2149, Appendix C, (24)

import Mathlib

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Appendix C, inequality (24), p. 2149 (the scalar
Auer–Gentile inequality): for any real sequence `a_1, a_2, …` and any `T`,
`∑_{t=1}^T a_t² / ‖a_{1:t}‖₂ ≤ 2 ‖a_{1:T}‖₂`, where `‖a_{1:t}‖₂ = (∑_{τ=1}^t a_τ²)^{1/2}` and
`0/0 = 0` (Lean's division convention). Rounds are 1-based; `a 0` is not used. -/
theorem eq_24 (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2)
      ≤ 2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by sorry

end AdaGrad.Diag
