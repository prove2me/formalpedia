-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_proposition_1_furthermore
-- name    : EndoRefLA.PartialPPE.proposition_1_furthermore
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:47.170153+00:00
-- url     : https://prove2.me/theorems/66eb5cab-2f1f-4ac3-9c00-0d3283e0369e
-- title:
--   Proposition 1, "Furthermore", p. 14 — X*_ex(Λ) is constant for Λ ≥ λmax and injective on [1, λmax)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$. The multipliers $\nu_G,\nu_L$ satisfy their root equations, and $\lambda_{\max}$ is given by (6). For each $\Lambda\ge1$, let $X^*_{\rm ex}(\Lambda)$ be an optimal solution of (4) with degree of loss aversion $\Lambda$.
--
--   Then:
--   1. $X^*_{\rm ex}(\Lambda)$ does not depend on $\Lambda$ for $\Lambda\in[\lambda_{\max},+\infty)$:
--   $$\Lambda_1,\Lambda_2\ge\lambda_{\max}\implies X^*_{\rm ex}(\Lambda_1)=X^*_{\rm ex}(\Lambda_2)\ \text{a.s.};$$
--   2. for any $1\le\Lambda_1<\Lambda_2<\lambda_{\max}$, $X^*_{\rm ex}(\Lambda_1)\ne X^*_{\rm ex}(\Lambda_2)$, that is, they differ on a set of positive probability.
--
--   So the range of loss aversion that matters for problem (4) is $[1,\lambda_{\max}]$. The proof of Theorem 3 uses both facts.
--
--   **Formalization Note.** The family $X^*_{\rm ex}(\cdot)$ is an arbitrary choice of optimal solutions; by Theorem 1 each is unique a.s., so nothing depends on the choice. "$\ne$" means "not a.s. equal".
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 14 (PDF 14), Proposition 1, last sentence ("Furthermore, …")

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proposition 1, "Furthermore", p. 14: `X*_ex(Λ)` does not depend on `Λ ∈ [λmax, +∞)`, and
`X*_ex(Λ₁) ≠ X*_ex(Λ₂)` for `1 ≤ Λ₁ < Λ₂ < λmax`. `Xex Λ` is any optimal solution of (4) with
degree of loss aversion `Λ`. -/
theorem proposition_1_furthermore
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    (∀ Λ₁ Λ₂ : ℝ, lamMax P ρ x0 α u B0 νG νL ≤ (Λ₁ : EReal) → lamMax P ρ x0 α u B0 νG νL ≤ (Λ₂ : EReal) →
      Xex Λ₁ =ᵐ[P] Xex Λ₂) ∧
    (∀ Λ₁ Λ₂ : ℝ, 1 ≤ Λ₁ → Λ₁ < Λ₂ → (Λ₂ : EReal) < lamMax P ρ x0 α u B0 νG νL →
      ¬ (Xex Λ₁ =ᵐ[P] Xex Λ₂)) := by sorry

end EndoRefLA.PartialPPE
