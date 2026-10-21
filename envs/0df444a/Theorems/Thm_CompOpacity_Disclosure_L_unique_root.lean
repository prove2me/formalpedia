-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_L_unique_root
-- name    : CompOpacity.Disclosure.L_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:39.241552+00:00
-- url     : https://prove2.me/theorems/78d0eeab-6bc2-4342-8430-a1e9e90df3d1
-- title:
--   pp. 37–38 — for a ∈ (0, 1/2), L has a unique positive root Δ, and L(x) < 0 iff x > Δ
-- statement:
--   Let $a \in (0, \tfrac12)$ and let $L(x) = A_0 + A_1x + A_2x^2 + A_3x^3 + A_4x^4$ be the quartic of (52)–(53). Then there is $\Delta > 0$ with $L(\Delta) = 0$, $\Delta$ is the only positive root of $L$, and for every $x > 0$,
--   $$L(x) < 0 \iff x > \Delta.$$
--
--   Combined with (50)–(53) and the monotonicity of $m^{NC}$ in $n$, the root $\Delta$ yields the threshold $\hat n$ of Proposition 4.
--
--   **Formalization Note** The page states this for $a \in (0, \tfrac12]$, but at $a = \tfrac12$ the leading coefficient $A_4$ vanishes; the statement takes $a < \tfrac12$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), pp. 37–38, (52)–(54), proof of Proposition 4, Sub-step 2

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- pp. 37–38: for `a ∈ (0, 1/2)`, the quartic `L` of (53) has a unique positive root `Δ`, and for
`x > 0`, `L(x) < 0` if and only if `x > Δ`. (The page says `a ∈ (0, 1/2]`; at `a = 1/2`,
`A₄ = 0`.) -/
theorem L_unique_root (a : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) : ∃ Δ : ℝ, 0 < Δ ∧ Lpoly a Δ = 0 ∧ (∀ x : ℝ, 0 < x → Lpoly a x = 0 → x = Δ) ∧ ∀ x : ℝ, 0 < x → (Lpoly a x < 0 ↔ Δ < x) := by sorry

end CompOpacity.Disclosure
