-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_rstar_closed_form_no_accel
-- name    : AccelScal.UCMonopoly.rstar_closed_form_no_accel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:42.262033+00:00
-- url     : https://prove2.me/theorems/5d8bd146-9392-447c-bca3-a6947e4e5d36
-- title:
--   Appendix A.2, p. 18 — without accelerability, R*_uc = (1/Aβλ)^{1/(β−1)}, independent of r
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions and let $r>0$. Suppose the project is not accelerable ($\gamma=0$, so $\lambda\equiv\eta$), is scalable ($\beta>0$), and $A\beta\eta\ge1$. Then the unconstrained monopoly has exactly one optimal intensity on $[1,\bar R]$, namely the solution of $u'\lambda=1$:
--   $$R^*_{uc}=\Big\{\Big(\frac{1}{A\beta\eta}\Big)^{1/(\beta-1)}\Big\}.$$
--
--   The right-hand side does not involve $r$, which is the paper's argument for $\partial R^*_{uc}/\partial r=0$ in Proposition 1(v) when the project is not accelerable.
--
--   **Formalization Note** The hypothesis $A\beta\eta\ge1$ is added: otherwise the root of $u'\lambda=1$ lies below $\underline R=1$ and the optimum is $\underline R$ instead. The printed form $(1/A\beta\lambda)^{1/(\beta-1)}$ is kept, with $\lambda=\eta$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 18, Appendix A.2, after (A.5)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem rstar_closed_form_no_accel (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r)
    (hγ : T.γ = 0) (hβ : 0 < T.β) (hint : 1 ≤ T.A * T.β * T.η) :
    RstarUC T r = {(1 / (T.A * T.β * T.η)) ^ (1 / (T.β - 1))} := by sorry
end AccelScal.UCMonopoly
