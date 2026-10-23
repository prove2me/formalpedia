-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_lemma_C_8
-- name    : FoodDeliv.Decentral.lemma_C_8
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:17.738121+00:00
-- url     : https://prove2.me/theorems/28f8d5cf-d580-400e-a247-ccb79b1b6079
-- title:
--   Lemma C.8 (OA pp. 21–22), items 1, 3, 4 — intersections of pΛ1, p(μ − c/(R − p)), p(μ − √(μϕ/(R − p))); the thresholds λ1 < λ2
-- statement:
--   Let $\mu>0$, $c>0$, $c<R\mu$, $0<\phi<c$; write $f(p)=p\big(\mu-\frac{c}{R-p}\big)$, $g(p)=p\Big(\mu-\sqrt{\frac{\mu\phi}{R-p}}\Big)$, $h(\lambda)=\lambda\Big(R-\frac{\mu\phi}{(\mu-\lambda)^2}\Big)$, $\chi$ the root of $-R\chi^3-\mu\phi\chi+2\mu^2\phi$ in $[0,\mu]$, $\lambda_2=\mu-\chi$, $K=(\sqrt{R\mu}-\sqrt c)^2$, $M=\frac{2R(\mu-\chi)^2}{2\mu-\chi}$, $\lambda_1$ the smallest root of $h=K$ in $(0,\mu)$, and $T=\frac{\sqrt{c^3(c+8R\mu)}-c^2}{2R\mu}$. Then:
--
--   1. With $x=R-\frac{c^2}{\mu\phi}$: $f(x)=g(x)=\mu x\frac{c-\phi}{c}$; and for $0<p<R$, $g(p)\le f(p)$ if $p\le x$, and $g(p)>f(p)$ if $p>x$.
--   3. For every $\Lambda_1\in(0,\mu)$, $p\Lambda_1$ and $g$ meet at $p=R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}$, with value $\Lambda_1\big(R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}\big)$. $h$ is unimodal on $(0,\mu)$ with maximizer $\lambda_2\in(0,\mu)$ and maximum $h(\lambda_2)=M$. If $K<M$, the equation $h(\lambda)=K$ has exactly two roots $\lambda_1\le\lambda_1'$ in $(0,\mu)$, and $\lambda_1<\lambda_2$.
--   4. At $\Lambda_1=\frac{c-\phi}{c}\mu$ the three curves $p\Lambda_1$, $f$, $g$ meet at $\big(x,\mu x\frac{c-\phi}{c}\big)$. For $\Lambda_1\in(0,\mu)$: $\Lambda_1\le\frac{c-\phi}{c}\mu\iff R-\frac{c}{\mu-\Lambda_1}\le R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}$, and the same with $\ge$. If $\phi\le T$ then $\lambda_2\le\frac{c-\phi}{c}\mu$; if $\phi>T$ then $\lambda_2>\frac{c-\phi}{c}\mu$.
--
--   These comparisons decide which of the three profit curves of Corollary C.2 the restaurant's optimum lies on, and define the threshold $\lambda_1$ of Proposition 1.
--
--   **Formalization Note** Item 2 (the root $\lambda_3$, not used by Proposition 1) is not part of this statement. $c<R\mu$ (F4) and $\phi>0$ (F5) are added; at $\phi=0$ the maximum of $h$ over $(0,\mu)$ is not attained. The roots are taken in the open interval $(0,\mu)$: $0$ and $\mu$ are never roots of $h=K$ (at $\mu$ the formula is undefined). "Unimodal" is: strictly increasing on $(0,\lambda_2]$, strictly decreasing on $[\lambda_2,\mu)$. In item 4 the meeting of $f$ and $g$ is item 1; the statement adds that $p\Lambda_1$ passes through the same point.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix pp. 21–22, Lemma C.8 (items 1, 3, 4)

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Lemma C.8, Online Appendix pp. 21–22, items 1, 3 and 4: intersection points of the curves
`p Λ1`, `p (μ - c/(R - p))` and `p (μ - √(μϕ/(R - p)))`, with `χ = chi R μ ϕ`,
`λ2 = lam2 R μ ϕ = μ - χ` and `λ1 = lam1 R μ c ϕ` (the smallest root of
`λ (R - μϕ/(μ - λ)²) = (√(Rμ) - √c)²` in `(0, μ)`). Item 2 is not part of this statement. -/
theorem lemma_C_8 (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    -- 1. `p (μ - c/(R-p))` and `p (μ - √(μϕ/(R-p)))`
    ((R - c ^ 2 / (μ * ϕ)) * (μ - c / (R - (R - c ^ 2 / (μ * ϕ)))) =
        μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c) ∧
      (R - c ^ 2 / (μ * ϕ)) * (μ - Real.sqrt (μ * ϕ / (R - (R - c ^ 2 / (μ * ϕ))))) =
        μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c) ∧
      ∀ p : ℝ, 0 < p → p < R →
        (p ≤ R - c ^ 2 / (μ * ϕ) →
          p * (μ - Real.sqrt (μ * ϕ / (R - p))) ≤ p * (μ - c / (R - p))) ∧
        (R - c ^ 2 / (μ * ϕ) < p →
          p * (μ - Real.sqrt (μ * ϕ / (R - p))) > p * (μ - c / (R - p)))) ∧
    -- 3. `p Λ1` and `p (μ - √(μϕ/(R-p)))`
    (∀ Λ1 ∈ Set.Ioo 0 μ,
      (R - μ * ϕ / (μ - Λ1) ^ 2) *
          (μ - Real.sqrt (μ * ϕ / (R - (R - μ * ϕ / (μ - Λ1) ^ 2)))) =
        Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)) ∧
    -- 3. the curve `λ (R - μϕ/(μ-λ)²)` is unimodal on `(0, μ)`, with maximizer `λ2 = μ - χ`
    (lam2 R μ ϕ ∈ Set.Ioo 0 μ ∧
      StrictMonoOn (fun l => deliveryCurve R μ ϕ l) (Set.Ioc 0 (lam2 R μ ϕ)) ∧
      StrictAntiOn (fun l => deliveryCurve R μ ϕ l) (Set.Ico (lam2 R μ ϕ) μ) ∧
      deliveryCurve R μ ϕ (lam2 R μ ϕ) = 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) ∧
      IsGreatest ((fun l => deliveryCurve R μ ϕ l) '' Set.Ioo 0 μ)
        (2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ))) ∧
    -- 3. the two roots `λ1 ≤ λ'1` and `λ1 < λ2`
    ((Real.sqrt (R * μ) - Real.sqrt c) ^ 2 < 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) →
      (∃ l' : ℝ, lam1 R μ c ϕ ≤ l' ∧
        {l : ℝ | l ∈ Set.Ioo 0 μ ∧
            deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2} =
          {lam1 R μ c ϕ, l'}) ∧
      lam1 R μ c ϕ < lam2 R μ ϕ) ∧
    -- 4. the three curves at `Λ1 = ((c - ϕ)/c) μ`, and the order of the thresholds
    ((c - ϕ) / c * μ * (R - c ^ 2 / (μ * ϕ)) = μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c)) ∧
    (∀ Λ1 ∈ Set.Ioo 0 μ,
      (Λ1 ≤ (c - ϕ) / c * μ ↔ R - c / (μ - Λ1) ≤ R - μ * ϕ / (μ - Λ1) ^ 2) ∧
      (Λ1 ≥ (c - ϕ) / c * μ ↔ R - c / (μ - Λ1) ≥ R - μ * ϕ / (μ - Λ1) ^ 2)) ∧
    (ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) →
      lam2 R μ ϕ ≤ (c - ϕ) / c * μ) ∧
    ((Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) < ϕ →
      lam2 R μ ϕ > (c - ϕ) / c * μ) := by sorry

end FoodDeliv.Decentral
