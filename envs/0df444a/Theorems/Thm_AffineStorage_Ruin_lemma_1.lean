-- Prove2me | Theorems.Thm_AffineStorage_Ruin_lemma_1
-- name    : AffineStorage.Ruin.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:27.691958+00:00
-- url     : https://prove2.me/theorems/48c92691-8fc2-4164-a366-39d9f89017c9
-- title:
--   Lemma 1, p. 1285 (PDF 6) — integro-differential equation (4) for ϱ on x > 0
-- statement:
--   Let $\varrho(x)$ be the expected discounted penalty at ruin before the exponential horizon, as a function of the initial surplus $x$. Let $d$ be the claim density, $\mu$ the rate of the exponential upward jumps and $\lambda=\lambda_-+\lambda_+$. For every $x>0$, $\varrho$ is differentiable at $x$ and
--   $$-\varrho'(x)(p+rx)=\lambda_-\int_0^x d(y)\varrho(x-y)\,dy+\lambda_-\int_x^\infty d(y)e^{-\beta(y-x)}e^{-\gamma x}\,dy+\lambda_+\int_0^\infty\mu e^{-\mu y}\varrho(x+y)\,dy-(\alpha+\lambda+\nu)\varrho(x).$$
--
--   This is the equation (4) obtained by conditioning on the first event in a short time interval. The first integral covers a claim that does not cause ruin, the second a claim that causes ruin (with overshoot $x-y$ and undershoot $x$), and the third an upward jump. The last term combines discounting, the jump rates and the horizon. Transforming this equation in $x$ yields Proposition 1.
--
--   **Formalization Note.** Differentiability of $\varrho$ at every $x>0$ is part of the statement: the page uses $\varrho'(x)$ without proving that it exists.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1285 (PDF 6), Lemma 1, eq. (4)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem lemma_1 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (rho B P) x ∧
    -(deriv (rho B P) x) * (P.p + P.r * x) =
      P.lamMinus * (∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y))
      + P.lamMinus * (∫ y in Set.Ioi x,
          P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
      + P.lamPlus * (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * rho B P (x + y))
      - (P.α + P.lam + P.ν) * rho B P x := by sorry

end AffineStorage.Ruin
