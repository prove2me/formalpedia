-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_eq_50_53
-- name    : CompOpacity.Disclosure.eq_50_53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:42.912713+00:00
-- url     : https://prove2.me/theorems/ec3aec97-7e3b-482d-86f0-6ac9b03a7fc1
-- title:
--   (50)–(53), p. 37 — the difference of the marginal payoffs at b = 1 and b = 0 is a positive multiple of L(n/(q+m))
-- statement:
--   Let $a \in (0, \tfrac12)$, $q, n > 0$ and $m \ge 0$. With $L$ the quartic of (52)–(53),
--   $$\frac{m + q - (1-2a)n}{2(1-2a)[q + m + (1-2a)n]^3} - \frac{m + q - (1-a)(1-4a)n}{2(1-a)^2[q + m + (1-a)n]^3} = \frac{(q+m)^4}{2(1-a)^2(1-2a)}\cdot\frac{L\big(\tfrac{n}{q+m}\big)}{[q + m + (1-a)n]^3\,[q + m + (1-2a)n]^3}.$$
--
--   The left side is (50): at $m = m^{NC}$ it equals $\partial\Pi^*_i/\partial m_i$, because the first-order condition (35) replaces $c_m m^{NC}$ by the no-competition marginal benefit. So the competitive FI wants to disclose less than $m^{NC}$ exactly when $L(n/(q + m^{NC})) < 0$.
--
--   **Formalization Note** The page evaluates the identity at $m = m^{NC}$; it is stated for every $m \ge 0$, which is what the algebra shows.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 37, (50)–(53), proof of Proposition 4, Sub-step 2

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- (50)–(53), p. 37: for `a ∈ (0, 1/2)`, `q, n > 0` and every `m ≥ 0`, the difference of the
gross marginal payoffs at `b = 1` and at `b = 0` (the right-hand side of (50)) equals the quartic
expression (51) in `n/(q + m)`:
`(q + m)⁴/(2(1 − a)²(1 − 2a)) · L(n/(q + m)) / ([q + m + (1 − a)n]³[q + m + (1 − 2a)n]³)`, with
`L` the polynomial (52)–(53). The page evaluates it at `m = mᴺᶜ`; the identity holds at every
`m ≥ 0`. -/
theorem eq_50_53 (a q n t : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (ht : 0 ≤ t) : margStar a q n t - margNC a q n t = (q + t) ^ 4 / (2 * (1 - a) ^ 2 * (1 - 2 * a)) * Lpoly a (n / (q + t)) / ((q + t + (1 - a) * n) ^ 3 * (q + t + (1 - 2 * a) * n) ^ 3) := by sorry

end CompOpacity.Disclosure
