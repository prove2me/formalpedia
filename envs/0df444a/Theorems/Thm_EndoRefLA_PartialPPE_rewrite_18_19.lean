-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_rewrite_18_19
-- name    : EndoRefLA.PartialPPE.rewrite_18_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:50.159033+00:00
-- url     : https://prove2.me/theorems/ce288982-c51a-478e-8c11-da2605331997
-- title:
--   Proof of Theorem 3, p. 34 — the objective of (18) equals ((1+(1+α)η)/(1+α))·V_Λ(X|B0) + const, Λ as in (19)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   For $\eta>0$, let
--   $$\Lambda(\eta)=\frac1\alpha\Big((1+\alpha)\frac{1+(1+\alpha\lambda)\eta}{1+(1+\alpha)\eta}-1\Big).$$
--   1. For every $\eta>0$ and every prospect $X$,
--   $$V_\lambda(X\mid X)+\eta\,V_\lambda(X\mid B_0)=\frac{1+(1+\alpha)\eta}{1+\alpha}\,V_{\Lambda(\eta)}(X\mid B_0)+\frac{\alpha}{1+\alpha}\,\mathbb E[u(B_0)].$$
--   2. If $\lambda>1$, then $\Lambda(\eta)\in(1,\lambda)$ for every $\eta>0$, $\eta\mapsto\Lambda(\eta)$ is strictly increasing on $(0,\infty)$, and every $\Lambda\in(1,\lambda)$ equals $\Lambda(\eta)$ for some $\eta>0$.
--
--   The Lagrangian of problem (17) is therefore, up to a positive factor and a constant, the objective of problem (4) with the lower degree of loss aversion $\Lambda(\eta)$. This links the partially endogenous model to the exogenous-reference optima.
--
--   **Formalization Note.** The paper prints the constant as $-(1+\eta)u(B_0)$ (the term $-\eta f^{-1}_{B_0}(c_0)$ of (18) is left out on both sides here). Expanding both sides gives $+\frac{\alpha}{1+\alpha}\mathbb E[u(B_0)]$, which is the constant stated here. It does not depend on $X$, so the paper's argument is unaffected. The identity holds in the extended reals for every $X$: if $\mathbb E[u(X)]=-\infty$, both sides are $-\infty$. Part 2 is implicit in "corresponding $\eta_1<\eta_2$ through the relation (19)".
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 34 (PDF 34), proof of Theorem 3, (18)–(19); constant corrected

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 3, p. 34: the objective of (18) rewritten through `Λ` of (19), with the
constant corrected to `+ (α/(1+α)) E[u(B0)]`; and the properties of `η ↦ Λ(η)` used there. -/
theorem rewrite_18_19
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    (∀ η : ℝ, 0 < η → ∀ X : Ω → ℝ,
      V P α u u0 lam X X + (η : EReal) * V P α u u0 lam X B0 =
        (((1 + (1 + α) * η) / (1 + α) : ℝ) : EReal) * V P α u u0 (LamEta α lam η) X B0 +
          ((α / (1 + α) : ℝ) : EReal) * Ex P (fun ω => uE u u0 (B0 ω))) ∧
    (1 < lam →
      (∀ η : ℝ, 0 < η → LamEta α lam η ∈ Set.Ioo 1 lam) ∧
      StrictMonoOn (LamEta α lam) (Set.Ioi 0) ∧
      ∀ Λ ∈ Set.Ioo 1 lam, ∃ η : ℝ, 0 < η ∧ LamEta α lam η = Λ) := by sorry

end EndoRefLA.PartialPPE
