-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_eq_46_47
-- name    : CompOpacity.Disclosure.eq_46_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:49.874339+00:00
-- url     : https://prove2.me/theorems/d333eb71-577c-4815-93de-7ed419b691b5
-- title:
--   (46)–(47), p. 36 (a < 1/2 added) — at b = 1 the disclosure equilibrium m* > 0 solves (46) iff n < q/(1−2a); otherwise m* = 0
-- statement:
--   At competition intensity $b = 1$, let $a \in [0, \tfrac12)$ and $q, \bar\theta > 0$. There is $c_0$ such that for every $c_m \ge c_0$ and every $n > 0$ the disclosure equilibrium is unique and symmetric, $(m^*, m^*)$, and:
--   1. if $n < q/(1-2a)$, then $m^* > 0$ and it solves (46),
--   $$\frac{m^* + q - (1-2a)n}{2(1-2a)[q + m^* + (1-2a)n]^3} - c_m m^* = 0;$$
--   2. if $n \ge q/(1-2a)$, then $m^* = 0$ (47).
--
--   This is Step 1 of the proof of Proposition 4: the competitive disclosure choice, to be compared with $m^{NC}$.
--
--   **Formalization Note** $a < \tfrac12$ is added (no linear investor equilibrium at $a = \tfrac12$, $b = 1$). "$c_m$ sufficiently large" is $\exists c_0\, \forall c_m \ge c_0$, uniform in $n$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 36, (45)–(47), proof of Proposition 4, Step 1

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- (46)–(47), p. 36: at competition intensity `b = 1` and `a ∈ [0, 1/2)`, for `c_m` sufficiently
large (one bound `c₀` for all `n > 0`), the disclosure equilibrium is unique and symmetric,
`m = (m*, m*)`; if `n < q/(1 − 2a)` then `m* > 0` solves (46),
`(m* + q − (1 − 2a)n)/(2(1 − 2a)[q + m* + (1 − 2a)n]³) − c_m m* = 0`, and if `n ≥ q/(1 − 2a)` then
`m* = 0` (47). The bound `a < 1/2` is added (no linear investor equilibrium at `a = 1/2`,
`b = 1`). -/
theorem eq_46_47 (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n : ℝ, 0 < n → ∃ mS : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (n < q / (1 - 2 * a) → 0 < mS ∧ margStar a q n mS - cm * mS = 0) ∧ (q / (1 - 2 * a) ≤ n → mS = 0) := by sorry

end CompOpacity.Disclosure
