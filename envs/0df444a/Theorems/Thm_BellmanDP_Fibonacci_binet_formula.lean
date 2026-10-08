-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_binet_formula
-- name    : BellmanDP.Fibonacci.binet_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:44:07.735986+00:00
-- url     : https://prove2.me/theorems/a9444785-dc2e-4ab1-b862-89976bce8afa
-- title:
--   Chapter I, Eqs. (22.5)–(22.6) — explicit formula for $F_n$ and $F_{n+1}/F_n \to (1+\sqrt5)/2$
-- statement:
--   Let $F_0 = F_1 = 1$, $F_n = F_{n-1} + F_{n-2}$ for $n \ge 2$, and
--   $$r_1 = \frac{1 + \sqrt5}{2}, \qquad r_2 = \frac{1 - \sqrt5}{2}.$$
--   Then for every $n \ge 0$
--   $$F_n = \frac{r_2 - 1}{r_2 - r_1}\, r_1^{\,n} + \frac{1 - r_1}{r_2 - r_1}\, r_2^{\,n},$$
--   and
--   $$\frac{F_{n+1}}{F_n} \to r_1 \quad (n \to \infty).$$
--
--   The ratio limit is what justifies the golden-section rule Bellman mentions: for large $n$ the first two evaluation points sit at distance $L / r_1$ from either end of the interval.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, Eqs. (22.5)-(22.6) and the sentence following them, p. 36

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

open Filter Topology

/-- Bellman, Ch. I, § 22, Eqs. (22.5)–(22.6), p. 36: with `r₁ = (1 + √5)/2` and `r₂ = (1 − √5)/2`,
`F_n = ((r₂ − 1)/(r₂ − r₁)) r₁ⁿ + ((1 − r₁)/(r₂ − r₁)) r₂ⁿ` for every `n`; and
`F_{n+1}/F_n → r₁` as `n → ∞`. -/
theorem binet_formula :
    (∀ n : ℕ, (bookFib n : ℝ) =
      ((1 - Real.sqrt 5) / 2 - 1) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 + Real.sqrt 5) / 2) ^ n +
        (1 - (1 + Real.sqrt 5) / 2) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 - Real.sqrt 5) / 2) ^ n) ∧
    Tendsto (fun n : ℕ => (bookFib (n + 1) : ℝ) / bookFib n) atTop
      (𝓝 ((1 + Real.sqrt 5) / 2)) := by sorry

end BellmanDP.Fibonacci
