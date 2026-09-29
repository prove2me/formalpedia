-- Prove2me | Theorems.Thm_DualSSD_Duality_secondPerformance_eq_expectedShortfall
-- name    : DualSSD.Duality.secondPerformance_eq_expectedShortfall
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:35:46.964463+00:00
-- url     : https://prove2.me/theorems/58859ace-7c1a-463f-bbea-6765822f8d22
-- title:
--   Eq. (2.4) — $F_X^{(2)}(\eta)$ is the expected shortfall $\mathbb E\max(\eta-X,0)$
-- statement:
--   Let $X$ be a random variable with $\mathbb E|X|<\infty$, with law $P_X$ on $\mathbb R$. For every target value $\eta\in\mathbb R$,
--   $$F_X^{(2)}(\eta)=\int_{-\infty}^{\eta}(\eta-\xi)\,P_X(d\xi)=\mathbb E\{\max(\eta-X,0)\}.$$
--
--   This expresses the area below the distribution function as the expected shortfall of $X$ below the target $\eta$; it is the form from which the paper computes the subdifferential (3.3) and the endpoint values of the conjugate.
--
--   **Formalization Note** The paper's third form $\mathbb P\{X\le\eta\}\,\mathbb E\{\eta-X\mid X\le\eta\}$ is not stated, because the conditional expectation is undefined when $\mathbb P\{X\le\eta\}=0$. The integrability hypothesis is the paper's standing assumption $\mathbb E|X|<\infty$.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 62, eq. (2.4)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.Duality

open MeasureTheory

/-- (2.4) (Ogryczak–Ruszczyński 2002, §2, p. 62): for a random variable `X` with `E|X| < ∞`
and every target `η`, the second performance function is the expected shortfall below `η`:
`F_X^(2)(η) = ∫_{(−∞, η]} (η − ξ) P_X(dξ) = E{max(η − X, 0)}`, where `P_X` is the law of `X`.
The paper's third form `P{X ≤ η} E{η − X | X ≤ η}` is not stated (it is undefined when
`P{X ≤ η} = 0`). -/
theorem secondPerformance_eq_expectedShortfall {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    Shared.secondPerformance P X η = ∫ ξ in Set.Iic η, (η - ξ) ∂(P.map X) ∧
      Shared.secondPerformance P X η = ∫ ω, max (η - X ω) 0 ∂P := by sorry

end DualSSD.Duality
