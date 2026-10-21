-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_lamPe_exists_unique
-- name    : EndoRefLA.PartialPPE.lamPe_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:50.113979+00:00
-- url     : https://prove2.me/theorems/b40b6050-1219-4a23-bf60-66df14e6a20f
-- title:
--   Proof of Theorem 3, p. 34 — for c̲ < c0 < c̄ a unique Λpe(c0) ∈ (1, λ∧λmax) meets the cost, and X*_ex(Λpe(c0)) solves (17)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Let $f:\mathbb R\to\mathbb R$ be strictly decreasing and continuous (the mental cost $f_{B_0}$). Let $\nu_G,\nu_L$ satisfy their root equations and $\lambda_{\max}$ be given by (6). For each $\Lambda\ge1$, let $X^*_{\rm ex}(\Lambda)$ be an optimal solution of (4) with degree of loss aversion $\Lambda$. Put
--   $$\underline c=f\big(V_\lambda(X^*_{\rm ex}(\lambda)\mid B_0)\big),\qquad \bar c=f\big(V_\lambda(X^*_{\rm ex}(1)\mid B_0)\big),$$
--   and let $\underline c<c_0<\bar c$. Then:
--   1. there is exactly one $\Lambda\in(1,\lambda\wedge\lambda_{\max})$ with $f\big(V_\lambda(X^*_{\rm ex}(\Lambda)\mid B_0)\big)=c_0$;
--   2. for that $\Lambda$, $X^*_{\rm ex}(\Lambda)\in\mathcal Y(B_0,c_0)$, and $V_\lambda(Y\mid Y)\le V_\lambda(X^*_{\rm ex}(\Lambda)\mid X^*_{\rm ex}(\Lambda))$ for all $Y\in\mathcal Y(B_0,c_0)$.
--
--   So $X^*_{\rm ex}(\Lambda_{\rm pe}(c_0))$ is optimal for (17), equivalently for (16), and hence is the partially endogenous PPE. The paper obtains the optimality from Lagrange duality.
--
--   **Formalization Note.** $f$ is evaluated at the real value of $V_\lambda(\cdot\mid B_0)$, which is finite for the optimal prospects (Theorem 1). Membership in $\mathcal Y(B_0,c_0)$ uses the domain convention of the definitions file.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 34 (PDF 34), proof of Theorem 3, last paragraph

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 3, p. 34, last paragraph: for `c̲ < c0 < c̄` there is a unique
`Λpe(c0) ∈ (1, λ ∧ λmax)` with `f_B0(V_λ(X*_ex(Λpe(c0))|B0)) = c0`, and `X*_ex(Λpe(c0))` is optimal
for (17), i.e. for (16). -/
theorem lamPe_exists_unique
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (f : ℝ → ℝ) (hf : StrictAnti f) (hfc : Continuous f)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ))
    (c0 : ℝ) (hc0 : c0 ∈ Set.Ioo (f (V P α u u0 lam (Xex lam) B0).toReal) (f (V P α u u0 lam (Xex 1) B0).toReal)) :
    (∃! Λ : ℝ, Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL) ∧ f (V P α u u0 lam (Xex Λ) B0).toReal = c0) ∧
    ∀ Λ ∈ Set.Ioo 1 (lamCap P ρ x0 α lam u B0 νG νL), f (V P α u u0 lam (Xex Λ) B0).toReal = c0 →
      Xex Λ ∈ Ycal P ρ x0 α u u0 lam B0 f c0 ∧ ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam (Xex Λ) (Xex Λ) := by sorry

end EndoRefLA.PartialPPE
