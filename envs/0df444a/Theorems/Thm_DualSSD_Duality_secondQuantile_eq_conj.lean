-- Prove2me | Theorems.Thm_DualSSD_Duality_secondQuantile_eq_conj
-- name    : DualSSD.Duality.secondQuantile_eq_conj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:38:12.157466+00:00
-- url     : https://prove2.me/theorems/2b5b6033-5587-4721-903a-48d954562b57
-- title:
--   Theorem 3.1(i) — $F_X^{(-2)}=[F_X^{(2)}]^*$
-- statement:
--   Let $X$ be a random variable with $\mathbb E|X|<\infty$. Then the second quantile function is the convex conjugate of the second performance function:
--   $$F_X^{(-2)}(p)=\big[F_X^{(2)}\big]^*(p)=\sup_{\eta\in\mathbb R}\big\{\eta p-F_X^{(2)}(\eta)\big\}\qquad\text{for every }p\in\mathbb R.$$
--   Here $F_X^{(-2)}(p)=\int_0^pF_X^{(-1)}(\alpha)\,d\alpha$ for $p\in[0,1]$ and $+\infty$ otherwise, so the identity includes that the conjugate is $+\infty$ for $p\notin[0,1]$, is $0$ at $p=0$ and equals $\mathbb E X$ at $p=1$.
--
--   This is the first half of the Fenchel duality between the absolute Lorenz curve and the second performance function; it turns pointwise comparisons of one into comparisons of the other.
--
--   **Formalization Note** Both sides are functions $\mathbb R\to\overline{\mathbb R}$ (`EReal`); the integrability hypothesis is the paper's standing assumption.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 65, Theorem 3.1(i)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile
import Definitions.Def_DualSSD_Duality_conj

namespace DualSSD.Duality

open MeasureTheory

/-- Theorem 3.1(i) (Ogryczak–Ruszczyński 2002, §3, p. 65): for every random variable `X` with
`E|X| < ∞`, `F_X^(−2) = [F_X^(2)]*` as functions `ℝ → ℝ̄` (in particular both are `+∞` off
`[0, 1]`). -/
theorem secondQuantile_eq_conj {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    secondQuantile P X = conj (fun η => ((Shared.secondPerformance P X η : ℝ) : EReal)) := by sorry

end DualSSD.Duality
