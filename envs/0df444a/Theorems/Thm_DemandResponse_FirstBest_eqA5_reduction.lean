-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_eqA5_reduction
-- name    : DemandResponse.FirstBest.eqA5_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:18:38.673987+00:00
-- url     : https://prove2.me/theorems/6c207952-d9b0-47ee-a522-1362fe1cf5c4
-- title:
--   (A.5) — V̄ is finite and negative, and V^FB = R₀(V̄/R₀)^{1+p/r}
-- statement:
--   In the demand-response model, let $V^{FB}$ be the producer's first-best value (2.6), the supremum of $J_P(\xi,\nu,\mathbb P)$ over contracts $\xi\in\mathcal C$ and admissible pairs $(\nu,\mathbb P)$ meeting the participation constraint $J_A(\xi,\nu,\mathbb P)\ge R_0$, and let
--   $$\bar V=\sup_{(\nu,\mathbb P)}\mathbb E^{\mathbb P}\Big[-e^{-\rho\left(\int_0^T(\delta X_t-c(\nu_t))dt-\frac h2\langle X\rangle_T\right)}\Big],\qquad \rho=\frac{rp}{r+p}.$$
--   Then $\bar V$ is a real number with $\bar V<0$, and
--   $$V^{FB}=R_0\Big(\frac{\bar V}{R_0}\Big)^{1+\frac pr}.$$
--
--   This is the Lagrangian reduction of the first-best problem: the contract is optimised out explicitly for each effort, leaving the single control problem $\bar V$, which no longer involves the contract or the Lagrange multiplier.
--
--   **Formalization Note** The reservation utility is written $R$ in (A.3)–(A.5) and $R_0$ in (2.6); they are the same constant. Finiteness and negativity of $\bar V$ are part of the statement, since (A.5) is meaningless otherwise; the paper establishes them on p. 27. The power is the real power of the positive number $\bar V/R_0$. In (A.3) the labels $\mathcal G^\nu$ and $\mathcal K^\nu$ are swapped relative to their definitions on the same page; (A.4) and (A.5) are consistent with $\mathcal K^\nu_T=\int_0^T(f(X_s)-c(\nu_s))ds$ and $\mathcal G^\nu_T=\int_0^Tg(X_s)ds+\frac h2\langle X\rangle_T$. Only the conclusion of (A.5) is stated, not the infimum over the multiplier.
-- source:
--   arXiv:1810.09063v3, Appendix A.2, (A.5) (p. 26)

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model

namespace DemandResponse.FirstBest

/-- Equation (A.5): `V̄` is a finite negative number `w` and the first-best value is
`V^FB = R₀ (V̄ / R₀)^{1 + p/r}`. -/
theorem eqA5_reduction {N d : ℕ} (P : Params N d) :
    ∃ w : ℝ, w < 0 ∧ Vbar P = (w : EReal) ∧
      VFB P = ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by sorry

end DemandResponse.FirstBest
