-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_lemma_1_uc
-- name    : AccelScal.UCMonopoly.lemma_1_uc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:03.263965+00:00
-- url     : https://prove2.me/theorems/cb4c1d0b-3547-49db-9558-cdfb0eae1ff8
-- title:
--   Lemma 1 (5), p. 5 — the R&D value of intensity R for an unconstrained monopoly equals (u(R)λ(R) − R)/(λ(R) + r)
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, let $r>0$ be the discount rate and $R>0$ an investment intensity. Let the discovery time $\tau_d$ be exponentially distributed with rate $\lambda(R)=\eta R^{\gamma}$. Then the R&D value of the unconstrained monopoly is the value of a perpetuity paying $u\lambda-R$ per period at the discount rate $\lambda+r$:
--   $$\mathbb E\Big[e^{-r\tau_d}\,u(R)-R\int_0^{\tau_d}e^{-rt}\,dt\Big]=\frac{u(R)\lambda(R)-R}{\lambda(R)+r}.$$
--
--   This is the unconstrained half of Lemma 1: it turns the stochastic problem (4) into the deterministic objective (5) whose comparative statics Proposition 1 describes.
--
--   **Formalization Note** Only (5) is posed; (6), for the financially constrained firm, needs the first passage of a geometric Brownian motion and is not part of this mission. The paper states (5) as a supremum over $R>0$; the pointwise identity posed here is what its proof computes, and the supremum statement follows from it.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 5, Lemma 1, (5)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem lemma_1_uc (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R) :
    ucPayoff T r R = (T.u R * T.lam R - R) / (T.lam R + r) := by sorry
end AccelScal.UCMonopoly
