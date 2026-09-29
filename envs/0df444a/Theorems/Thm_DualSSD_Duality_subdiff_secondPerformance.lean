-- Prove2me | Theorems.Thm_DualSSD_Duality_subdiff_secondPerformance
-- name    : DualSSD.Duality.subdiff_secondPerformance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:37:31.671986+00:00
-- url     : https://prove2.me/theorems/4b09c415-695d-4330-99c4-2a79acc3a1b8
-- title:
--   Eq. (3.3) — $\partial F_X^{(2)}(\eta)=[\mathbb P\{X<\eta\},\mathbb P\{X\le\eta\}]$
-- statement:
--   Let $X$ be a random variable with $\mathbb E|X|<\infty$. For every $\eta\in\mathbb R$ the subdifferential of the second performance function $F_X^{(2)}$ at $\eta$ is the closed interval
--   $$\partial F_X^{(2)}(\eta)=\big[\mathbb P\{X<\eta\},\ \mathbb P\{X\le\eta\}\big]. \tag{3.3}$$
--
--   Here $\partial f(\eta)$ is the set of $g$ with $f(\eta)+g(\xi-\eta)\le f(\xi)$ for all $\xi$. Combined with the definition of a $p$-quantile, (3.3) says that $p\in\partial F_X^{(2)}(\eta)$ exactly when $\eta$ is a $p$-quantile of $X$; this is the bridge between the conjugate of $F_X^{(2)}$ and the quantile function.
--
--   **Formalization Note** The integrability hypothesis is the paper's standing assumption $\mathbb E|X|<\infty$, which makes $F_X^{(2)}$ finite.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 65, eq. (3.3)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_conj

namespace DualSSD.Duality

open MeasureTheory

/-- (3.3) (Ogryczak–Ruszczyński 2002, §3, p. 65): for `E|X| < ∞` and every `η ∈ ℝ`, the
subdifferential of the second performance function is
`∂F_X^(2)(η) = [P{X < η}, P{X ≤ η}]`. -/
theorem subdiff_secondPerformance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    subdiff (Shared.secondPerformance P X) η =
      Set.Icc (P.real {ω | X ω < η}) (P.real {ω | X ω ≤ η}) := by sorry

end DualSSD.Duality
