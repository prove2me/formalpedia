-- Prove2me | Theorems.Thm_BellmanDP_Variational_cont_value_le_liminf
-- name    : BellmanDP.Variational.cont_value_le_liminf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:37:59.586626+00:00
-- url     : https://prove2.me/theorems/988ad25d-53d7-442f-be34-9bebec95eb7b
-- title:
--   Chapter IX, § 12, Eq. (12.17) — $f(c,T)\le\liminf_{n\to\infty} f(c,T,n)$
-- statement:
--   Let $F(x,y)$ and $G(x,y)$ satisfy the assumptions (11) of Chapter IX, Theorem 2, and let $c>0$, $T>0$. Then the value $f(c,T)$ of the continuous problem is at most the lower limit of the values of the discrete problems:
--   $$f(c,T)\le\liminf_{n\to\infty}f(c,T,n).$$
--   Equivalently, for every $\varepsilon>0$, $f(c,T,n)\ge f(c,T)-\varepsilon$ for all sufficiently large $n$.
--
--   This is the harder half of Theorem 2: every continuous control can be approximated by discrete ones without losing more than $\varepsilon$.
--
--   **Formalization Note** The lower limit is stated in its $\varepsilon$ form, which avoids Lean's conventions for `liminf` of a sequence not known to be bounded. The step count is the corrected $N=\lfloor Tn\rfloor$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 12, proof of Theorem 2, Eq. (12.17), p. 262

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Filter

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, proof of Theorem 2, Eq. (12.17), p. 262: under the
assumptions (11), for `c > 0` and `T > 0`, `f (c, T) ≤ lim inf_{n → ∞} f (c, T, n)`, i.e. for every
`ε > 0`, `f (c, T, n) ≥ f (c, T) − ε` for all sufficiently large `n`. -/
theorem cont_value_le_liminf (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      contValue (phiForm F) (phiForm G) c T - ε ≤ discreteValue (phiForm F) (phiForm G) c T n := by sorry

end BellmanDP.Variational
