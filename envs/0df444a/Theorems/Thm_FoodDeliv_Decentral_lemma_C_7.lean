-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_lemma_C_7
-- name    : FoodDeliv.Decentral.lemma_C_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:14.451826+00:00
-- url     : https://prove2.me/theorems/648f4714-dfd2-498d-89ec-2e570067e1c5
-- title:
--   Lemma C.7 (OA pp. 19–20), items 1, 2, 4 — properties of p(μ − √(μϕ/(R − p))): maximum 2R(μ − χ)²/(2μ − χ) at 2R(μ − χ)/(2μ − χ)
-- statement:
--   Let $\mu>0$, $c>0$, $c<R\mu$ and $0<\phi<c$, let $g(p)=p\Big(\mu-\sqrt{\frac{\mu\phi}{R-p}}\Big)$, and let $\chi=\chi(\phi)$ be the root of $-R\chi^3-\mu\phi\chi+2\mu^2\phi$ in $[0,\mu]$. Then:
--
--   1. $g(R-\phi/\mu)=0$.
--   2. $\chi$ is the unique root of $-R\chi^3-\mu\phi\chi+2\mu^2\phi$ in $[0,\mu]$; $g$ is unimodal on $(0,R-\phi/\mu]$, and
--   $$\max_{p\in(0,R-\phi/\mu]}g(p)=\frac{2R(\mu-\chi)^2}{2\mu-\chi},\qquad\operatorname*{arg\,max}_{p\in(0,R-\phi/\mu]}g(p)=\frac{2R(\mu-\chi)}{2\mu-\chi},$$
--   the maximizer being unique. Moreover $\chi(\phi)$ is strictly increasing and $\frac{2R(\mu-\chi(\phi))^2}{2\mu-\chi(\phi)}$ strictly decreasing in $\phi\in[0,c)$.
--   4. If $\phi\le\frac{\sqrt{c^3(c+8R\mu)}-c^2}{2R\mu}$, then $\frac{2R(\mu-\chi)}{2\mu-\chi}>R-\sqrt{\frac c\mu R}$.
--
--   $g$ is the restaurant's profit in the delivery-only regime where the platform charges its interior optimal fee.
--
--   **Formalization Note** Item 3 of the lemma is not part of this statement: as printed, its second equivalence fails at the boundary value $\phi=\frac{\sqrt{c^3(c+8R\mu)}-c^2}{2R\mu}$, where both sides of the comparison are equal (finding F9). $c<R\mu$ (F4) and $\phi>0$ (F5; at $\phi=0$ the zero of item 1 disappears) are added. "Unimodal" is: strictly increasing up to a point of the interval, strictly decreasing after it. "Increases/decreases in $\phi$" is read on the model's range $\phi\in[0,c)$.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix pp. 19–20, Lemma C.7 (items 1, 2, 4)

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Lemma C.7, Online Appendix pp. 19–20, items 1, 2 and 4: properties of
`p (μ - √(μϕ/(R - p)))` on `p ∈ (0, R - ϕ/μ]`, where `χ = chi R μ ϕ` is the unique root of
`-Rχ³ - μϕχ + 2μ²ϕ` in `[0, μ]`. "Unimodal" is: strictly increasing up to a point of the
interval and strictly decreasing after it. Item 3 is not part of this statement. -/
theorem lemma_C_7 (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    -- 1. the zero at `p = R - ϕ/μ`
    (R - ϕ / μ) * (μ - Real.sqrt (μ * ϕ / (R - (R - ϕ / μ)))) = 0 ∧
    -- 2. `χ` is the unique root in `[0, μ]`
    (chi R μ ϕ ∈ Set.Icc 0 μ ∧ chiCubic R μ ϕ (chi R μ ϕ) = 0 ∧
      ∀ x ∈ Set.Icc 0 μ, chiCubic R μ ϕ x = 0 → x = chi R μ ϕ) ∧
    -- 2. unimodal on `(0, R - ϕ/μ]`, with its maximum and unique maximizer
    (∃ m ∈ Set.Ioc 0 (R - ϕ / μ),
      StrictMonoOn (fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p)))) (Set.Ioc 0 m) ∧
      StrictAntiOn (fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p))))
        (Set.Icc m (R - ϕ / μ))) ∧
    IsGreatest ((fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p)))) '' Set.Ioc 0 (R - ϕ / μ))
      (2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ)) ∧
    {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - Real.sqrt (μ * ϕ / (R - q))) ≤ p * (μ - Real.sqrt (μ * ϕ / (R - p)))} =
      {2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ)} ∧
    -- 2. `χ` increases in `ϕ`, and the maximum decreases with `ϕ`
    StrictMonoOn (fun φ => chi R μ φ) (Set.Ico 0 c) ∧
    StrictAntiOn (fun φ => 2 * R * (μ - chi R μ φ) ^ 2 / (2 * μ - chi R μ φ)) (Set.Ico 0 c) ∧
    -- 4. comparison of the two maximizers
    (ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) →
      2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) > R - Real.sqrt (c / μ * R)) := by sorry

end FoodDeliv.Decentral
