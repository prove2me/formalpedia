-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_admissible_exp_moment_absX
-- name    : DemandResponse.FirstBest.admissible_exp_moment_absX
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T07:56:35.847881+00:00
-- url     : https://prove2.me/theorems/dfd7d230-384e-44d8-89e3-3294b17fae07
-- title:
--   Uniform exponential moments $\sup_{\mathbb P^\nu}\mathbb E[e^{c\int_0^T|X_t|dt}]<\infty$ over admissible pairs
-- statement:
--   In the demand-response model of Aïd, Possamaï and Touzi, let $X$ be the canonical consumption process on $\Omega=C([0,T],\mathbb R)$. For every real $c$,
--   $$\sup_{(\nu,\mathbb P)\ \text{admissible}}\ \mathbb E^{\mathbb P}\Big[\exp\Big(c\int_0^T|X_t|\,dt\Big)\Big]<\infty,$$
--   the supremum being over all admissible pairs, i.e. all weak solutions of $dX_t=-\alpha_t\cdot\mathbf 1\,dt+\sigma(\beta_t)\cdot dW_t$, $X_0$ given, with efforts $\alpha\in A$ and $\beta\in B=[\varepsilon,1]^d$.
--
--   Since the drift is bounded and the quadratic variation $\int_0^t|\sigma(\beta_s)|^2ds\le t\sum_j\sigma_j^2$ is bounded uniformly in the effort, the consumption has Gaussian-type tails uniformly over all efforts. This uniform integrability is what the paper uses implicitly when it bounds $\bar V$ on p. 27 by $\sup_{\mathbb P^\nu}\mathbb E^{\mathbb P^\nu}[-e^{-\rho((f-g)(X_0)\pm|f-g|'_\infty\int_0^T|X_t|dt)}]$, and it is what makes contracts built from $\int_0^TX_tdt$, such as the first-best contract (A.4), belong to the class $\mathcal C$ of (2.5).
--
--   **Formalization Note** Admissible pairs are the martingale-problem formulation of (2.1) on the canonical space: $X_0=X_0$ a.s., and $M_t=X_t-X_0+\int_0^t\alpha_s\cdot\mathbf 1ds$ and $M_t^2-\int_0^t|\sigma(\beta_s)|^2ds$ are martingales. The expectation is a lower Lebesgue integral in $[0,\infty]$; for $c\le0$ the statement is trivial.
-- source:
--   arXiv:1810.09063v3 (Aïd, Possamaï, Touzi), Appendix A.2, proof of Proposition A.3 (bounds on V̄), p. 27; integrability condition (2.5), p. 9

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model

open MeasureTheory

namespace DemandResponse.FirstBest

/-- Uniform exponential moments of the consumption path: for every real `c`,
`sup_{(ν, ℙ) admissible} E^ℙ[exp(c ∫₀ᵀ |X_t| dt)] < ∞`. -/
theorem admissible_exp_moment_absX {N d : ℕ} (P : Params N d) (c : ℝ) :
    (⨆ (ν : Control P) (Q : Measure (Path P)) (_ : Admissible P ν Q),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * ∫ s in (0 : ℝ)..P.T, |Xr P s ω|)) ∂Q) < ⊤ := by sorry

end DemandResponse.FirstBest
