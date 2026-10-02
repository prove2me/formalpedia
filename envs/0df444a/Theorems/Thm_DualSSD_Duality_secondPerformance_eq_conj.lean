-- Prove2me | Theorems.Thm_DualSSD_Duality_secondPerformance_eq_conj
-- name    : DualSSD.Duality.secondPerformance_eq_conj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:38:56.631977+00:00
-- url     : https://prove2.me/theorems/84d97046-5611-4dc2-96a3-f9ff071a20ac
-- title:
--   Theorem 3.1(ii) — $F_X^{(2)}=[F_X^{(-2)}]^*$
-- statement:
--   Let $X$ be a random variable with $\mathbb E|X|<\infty$. Then the second performance function is the convex conjugate of the second quantile function:
--   $$F_X^{(2)}(\eta)=\big[F_X^{(-2)}\big]^*(\eta)=\sup_{\alpha\in\mathbb R}\big\{\eta\alpha-F_X^{(-2)}(\alpha)\big\}\qquad\text{for every }\eta\in\mathbb R,$$
--   where $F_X^{(-2)}=+\infty$ off $[0,1]$, so effectively the supremum runs over $\alpha\in[0,1]$.
--
--   Together with part (i), this states that $F_X^{(2)}$ and $F_X^{(-2)}$ are mutually conjugate convex functions.
--
--   **Formalization Note** The conjugate is computed in `EReal`; terms with $F_X^{(-2)}(\alpha)=+\infty$ contribute $-\infty$. The integrability hypothesis is the paper's standing assumption.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 65, Theorem 3.1(ii)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile
import Definitions.Def_DualSSD_Duality_conj

namespace DualSSD.Duality

open MeasureTheory

/-- Theorem 3.1(ii) (Ogryczak–Ruszczyński 2002, §3, p. 65): for every random variable `X` with
`E|X| < ∞`, `F_X^(2) = [F_X^(−2)]*` as functions `ℝ → ℝ̄`. -/
theorem secondPerformance_eq_conj {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    (fun η => ((Shared.secondPerformance P X η : ℝ) : EReal)) = conj (secondQuantile P X) := by sorry

end DualSSD.Duality
