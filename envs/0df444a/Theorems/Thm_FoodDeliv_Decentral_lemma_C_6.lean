-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_lemma_C_6
-- name    : FoodDeliv.Decentral.lemma_C_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:13.747139+00:00
-- url     : https://prove2.me/theorems/eabffb16-72f8-4cb7-8e2b-e735b73a6be4
-- title:
--   Lemma C.6 (OA p. 19) — properties of p(μ − c/(R − p)): zero, unimodality, maximum (√(Rμ) − √c)² at R − √(cR/μ)
-- statement:
--   Let $\mu>0$, $c>0$, $c<R\mu$ and $0<\phi<c$, and let $f(p)=p\big(\mu-\frac{c}{R-p}\big)$. Then:
--
--   1. $f(R-c/\mu)=0$.
--   2. $f$ is unimodal on $(0,R-\phi/\mu]$ (strictly increasing up to some point of the interval, strictly decreasing after it), and
--   $$\max_{p\in(0,R-\phi/\mu]}f(p)=(\sqrt{R\mu}-\sqrt c)^2,\qquad \operatorname*{arg\,max}_{p\in(0,R-\phi/\mu]}f(p)=R-\sqrt{\tfrac{c}{\mu}R},$$
--   the maximizer being unique.
--   3. $R-\sqrt{\frac c\mu R}\le R-\frac{c^2}{\mu\phi}\iff\phi\ge\sqrt{\frac{c^3}{R\mu}}$, and $R-\sqrt{\frac c\mu R}\ge R-\frac{c^2}{\mu\phi}\iff\phi\le\sqrt{\frac{c^3}{R\mu}}$.
--
--   $f$ is the restaurant's profit when tech-savvy and traditional customers both walk in or deliver at the walk-in join-up-to level.
--
--   **Formalization Note** $c<R\mu$ is the standing hypothesis the paper uses implicitly (finding F4: without it the maximizer lies outside the interval). $\phi>0$ is added (finding F5): item 3 divides by $\phi$, and at $\phi=0$ the interval's endpoint $p=R$ makes $c/(R-p)$ a division by zero, which Lean evaluates as $0$.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 19, Lemma C.6

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Lemma C.6, Online Appendix p. 19: properties of `p (μ - c/(R - p))` on `p ∈ (0, R - ϕ/μ]`.
"Unimodal" is: strictly increasing up to a point of the interval and strictly decreasing after
it. -/
theorem lemma_C_6 (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    -- 1. the zero at `p = R - c/μ`
    (R - c / μ) * (μ - c / (R - (R - c / μ))) = 0 ∧
    -- 2. unimodal on `(0, R - ϕ/μ]`, with its maximum and unique maximizer
    (∃ m ∈ Set.Ioc 0 (R - ϕ / μ),
      StrictMonoOn (fun p => p * (μ - c / (R - p))) (Set.Ioc 0 m) ∧
      StrictAntiOn (fun p => p * (μ - c / (R - p))) (Set.Icc m (R - ϕ / μ))) ∧
    IsGreatest ((fun p => p * (μ - c / (R - p))) '' Set.Ioc 0 (R - ϕ / μ))
      ((Real.sqrt (R * μ) - Real.sqrt c) ^ 2) ∧
    {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - c / (R - q)) ≤ p * (μ - c / (R - p))} =
      {R - Real.sqrt (c / μ * R)} ∧
    -- 3. the position of the maximizer relative to `R - c²/(μϕ)`
    (R - Real.sqrt (c / μ * R) ≤ R - c ^ 2 / (μ * ϕ) ↔ ϕ ≥ Real.sqrt (c ^ 3 / (R * μ))) ∧
    (R - Real.sqrt (c / μ * R) ≥ R - c ^ 2 / (μ * ϕ) ↔ ϕ ≤ Real.sqrt (c ^ 3 / (R * μ))) := by sorry

end FoodDeliv.Decentral
