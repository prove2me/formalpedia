-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_value_strictMono
-- name    : EndoRefLA.PartialPPE.value_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:48.576694+00:00
-- url     : https://prove2.me/theorems/c76fe25d-8e2d-4904-80a5-4579e6b1fc80
-- title:
--   Proof of Theorem 3, p. 34 — Λ ↦ V_λ(X*_ex(Λ)|B0) is strictly increasing on [1, λ∧λmax)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Let $\nu_G,\nu_L$ satisfy their root equations, let $\lambda_{\max}$ be given by (6), and for each $\Lambda\ge1$ let $X^*_{\rm ex}(\Lambda)$ be an optimal solution of (4) with degree of loss aversion $\Lambda$. Then
--   $$1\le\Lambda_1<\Lambda_2<\lambda\wedge\lambda_{\max}\implies V_\lambda(X^*_{\rm ex}(\Lambda_1)\mid B_0)<V_\lambda(X^*_{\rm ex}(\Lambda_2)\mid B_0).$$
--
--   A higher degree of loss aversion in the optimization brings the optimum closer to $B_0$ as judged by the intrinsic preference. Together with continuity, this makes the degree of loss aversion that meets a given mental cost unique.
--
--   **Formalization Note.** The values are finite (item `value_continuous`), so the statement compares their real values.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 34 (PDF 34), proof of Theorem 3, "Therefore, Vλ(X*ex(Λ)|B0) is strictly increasing in Λ ∈ [1, λ ∧ λmax)"

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 3, p. 34: `V_λ(X*_ex(Λ)|B0)` is strictly increasing in
`Λ ∈ [1, λ ∧ λmax)`. -/
theorem value_strictMono
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    StrictMonoOn (fun Λ : ℝ => (V P α u u0 lam (Xex Λ) B0).toReal) (Set.Ico 1 (lamCap P ρ x0 α lam u B0 νG νL)) := by sorry

end EndoRefLA.PartialPPE
