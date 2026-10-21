-- Prove2me | Theorems.Thm_DeliveryDisclosure_InfoEffort_lemma_1_ii
-- name    : DeliveryDisclosure.InfoEffort.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:19.623986+00:00
-- url     : https://prove2.me/theorems/6e8bb40e-287e-49a6-bfd4-a98c86773892
-- title:
--   Lemma 1, item 2, p. 11 — under (16) the optimal plan exists, is unique, and solves (13)–(14)
-- statement:
--   Under the standing assumptions, including the capacity condition (16), fix an effort $\phi\in[0,1]$. Then there is exactly one optimal plan $(p^*,t^*)$, i.e. one feasible plan maximizing $\Pi(p,t,\phi)$ over all feasible plans. Every optimal plan $(p,t)$, with $\lambda=\lambda(p,t,\phi)$, satisfies the delivery-time equation (13)
--   $$\beta_r\rho\,(\mu-\lambda)\,e^{-(\mu-\lambda)t}=\beta_t$$
--   and the price equation (14)
--   $$p=b\phi+c+\frac{\beta_t\lambda t}{\mu-\lambda}+\frac{\omega_\theta\Lambda}{\Lambda-\lambda}.$$
--
--   This is the first step of the paper's two-step approach: it determines $p^*(\phi)$, $t^*(\phi)$ and hence $\lambda^*(\phi)$ and $\Pi^*(\phi)$, which the second step optimizes over $\phi$.
--
--   **Formalization Note** The page's hypothesis of item 2 is $\mu\ge\bar S\Lambda+\beta_t/(\beta_r\rho)$; it follows from the standing condition (16) since $e>1$. The page's sequential description (first $t^*(p,\phi)$ from (13), then $p^*(\phi)$ from (14)) is stated for the joint optimum. Item 1 of the lemma, the corner case, is excluded by (16) and not formalized.
-- source:
--   Leng, Becerril-Arreola, Parlar & Ferguson, Disclosing Delivery Performance Information (authors' preprint, April 2nd, 2023), p. 11, Lemma 1, item 2, eqs. (13)–(14); proof pp. OA-2 – OA-5

import Mathlib
import Definitions.Def_DeliveryDisclosure_InfoEffort_Model

namespace DeliveryDisclosure.InfoEffort

/-- Lemma 1, item 2, p. 11 (restated for the joint optimum): under the standing capacity
condition (16), for every effort `ϕ ∈ [0, 1]` there is exactly one optimal plan `(p*, t*)`, and every
optimal plan satisfies the delivery-time equation (13) and the price equation (14), with `λ` the
demand rate at that plan. -/
theorem lemma_1_ii (P : Params) (hP : Standing P) (ϕ : ℝ) (hϕ : ϕ ∈ Set.Icc (0 : ℝ) 1) :
    (∃! x : ℝ × ℝ, IsOptimal P ϕ x) ∧
      ∀ x : ℝ × ℝ, IsOptimal P ϕ x →
        P.βr * P.ρ * (P.μ - dem P x.1 x.2 ϕ) * Real.exp (-(P.μ - dem P x.1 x.2 ϕ) * x.2) = P.βt ∧
        x.1 = P.b * ϕ + P.c + P.βt * dem P x.1 x.2 ϕ * x.2 / (P.μ - dem P x.1 x.2 ϕ) +
          ωθ P ϕ * P.Λ / (P.Λ - dem P x.1 x.2 ϕ) := by sorry

end DeliveryDisclosure.InfoEffort
