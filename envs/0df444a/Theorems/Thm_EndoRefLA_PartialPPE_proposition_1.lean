-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_proposition_1
-- name    : EndoRefLA.PartialPPE.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:55.438683+00:00
-- url     : https://prove2.me/theorems/bae0bdcc-0567-4610-a906-8a6e04c39057
-- title:
--   Proposition 1 (i)–(iii), p. 14 — X*_ex(λ) ≥ B0, = B0 or ≤ B0 iff λ ≥ λmax; νG, νL well defined
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Let $\bar z=\operatorname{esssup}(u'(B_0)/\rho)$ and $\underline z=\operatorname{essinf}(u'(B_0)/\rho)$.
--
--   1. If $\mathbb E[\rho B_0]<x_0$, there is a unique $\nu_G>0$ with $\mathbb E[\rho((u')^{-1}(\nu_G\rho)\vee B_0)]=x_0$. If $\mathbb E[\rho B_0]>x_0$, there is a unique $\nu_L>0$ with $\mathbb E[\rho((u')^{-1}(\nu_L\rho)\wedge B_0)]=x_0$.
--   2. With these multipliers, define
--   $$\lambda_{\max}=\begin{cases}\max\Big(\frac{(1+\alpha)(\nu_G/\underline z)-1}{\alpha},1\Big), & \mathbb E[\rho B_0]<x_0,\\ \max\Big(\frac{(1+\alpha)(\bar z/\nu_L)-1}{\alpha},1\Big), & \mathbb E[\rho B_0]>x_0,\\ \frac{(1+\alpha)(\bar z/\underline z)-1}{\alpha}, & \mathbb E[\rho B_0]=x_0.\end{cases}$$
--      Then $\lambda_{\max}\in[1,+\infty]$, and for every optimal solution $X^*_{\rm ex}(\lambda)$ of (4):
--      - (i) when $\mathbb E[\rho B_0]<x_0$, $X^*_{\rm ex}(\lambda)\ge B_0$ a.s. if and only if $\lambda\ge\lambda_{\max}$, in which case $X^*_{\rm ex}(\lambda)=(u')^{-1}(\nu_G\rho)\vee B_0$;
--      - (ii) when $\mathbb E[\rho B_0]=x_0$, $X^*_{\rm ex}(\lambda)=B_0$ if and only if $\lambda\ge\lambda_{\max}$;
--      - (iii) when $\mathbb E[\rho B_0]>x_0$, $X^*_{\rm ex}(\lambda)\le B_0$ a.s. if and only if $\lambda\ge\lambda_{\max}$, in which case $X^*_{\rm ex}(\lambda)=(u')^{-1}(\nu_L\rho)\wedge B_0$.
--
--   The threshold $\lambda_{\max}$ separates the degrees of loss aversion at which the optimum is gains-only or losses-only from those at which it mixes gains and losses.
--
--   **Formalization Note.** Equalities are $P$-a.s. $\lambda_{\max}$ lives in the extended reals; $\nu_G/\underline z=+\infty$ when $\underline z=0$, $\bar z/\nu_L=+\infty$ when $\bar z=+\infty$, and $\lambda_{\max}=1$ when $\underline z=+\infty$ (that is, $B_0=0$ a.s.). The price $\mathbb E[\rho B_0]$ may be $+\infty$, which falls in case (iii). The statement takes any $\nu_G,\nu_L$ satisfying the root equations; by the first clause they are the unique ones.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 14 (PDF 14), (6) and Proposition 1 (i)–(iii); well-definedness of νG, νL and λmax ∈ [1, +∞] from the proof, pp. 32–33

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- (6) and Proposition 1 (i)–(iii), p. 14, with the well-definedness of `νG`, `νL` and
`λmax ∈ [1, +∞]` (proof, pp. 32–33). -/
theorem proposition_1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    (price P ρ B0 < ENNReal.ofReal x0 →
      ∃! ν : ℝ, 0 < ν ∧
        price P ρ (fun ω => max (Iinv u (ν * ρ ω)) (B0 ω)) = ENNReal.ofReal x0) ∧
    (ENNReal.ofReal x0 < price P ρ B0 →
      ∃! ν : ℝ, 0 < ν ∧
        price P ρ (fun ω => min (Iinv u (ν * ρ ω)) (B0 ω)) = ENNReal.ofReal x0) ∧
    ∀ νG νL : ℝ,
      (price P ρ B0 < ENNReal.ofReal x0 →
        0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0) →
      (ENNReal.ofReal x0 < price P ρ B0 →
        0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0) →
      ∀ X : Ω → ℝ, IsOptEx P ρ x0 α u u0 B0 lam X →
        (1 : EReal) ≤ lamMax P ρ x0 α u B0 νG νL ∧
        -- (i)
        (price P ρ B0 < ENNReal.ofReal x0 →
          ((∀ᵐ ω ∂P, B0 ω ≤ X ω) ↔ lamMax P ρ x0 α u B0 νG νL ≤ (lam : EReal)) ∧
          (lamMax P ρ x0 α u B0 νG νL ≤ (lam : EReal) →
            X =ᵐ[P] fun ω => max (Iinv u (νG * ρ ω)) (B0 ω))) ∧
        -- (ii)
        (price P ρ B0 = ENNReal.ofReal x0 →
          (X =ᵐ[P] B0 ↔ lamMax P ρ x0 α u B0 νG νL ≤ (lam : EReal))) ∧
        -- (iii)
        (ENNReal.ofReal x0 < price P ρ B0 →
          ((∀ᵐ ω ∂P, X ω ≤ B0 ω) ↔ lamMax P ρ x0 α u B0 νG νL ≤ (lam : EReal)) ∧
          (lamMax P ρ x0 α u B0 νG νL ≤ (lam : EReal) →
            X =ᵐ[P] fun ω => min (Iinv u (νL * ρ ω)) (B0 ω))) := by sorry

end EndoRefLA.PartialPPE
