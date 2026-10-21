-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_theorem_1
-- name    : EndoRefLA.PartialPPE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:49.782083+00:00
-- url     : https://prove2.me/theorems/ad1f94c3-3d78-41d3-be78-f624014a6255
-- title:
--   Theorem 1, p. 12 — the unique optimum of (4) is the three-region prospect (5) with a budget-exhausting multiplier ν > 0
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Problem (4) is to maximize $V_\lambda(X\mid B_0)$ over $X\ge0$ with $\mathbb E[\rho X]\le x_0$. There is a multiplier $\nu>0$ such that the prospect
--   $$X^*_{\rm ex}(\lambda)=\begin{cases}(u')^{-1}(\nu\rho), & \rho<\frac1\nu u'(B_0),\\ B_0, & \frac1\nu u'(B_0)\le\rho\le\frac{1+\alpha\lambda}{1+\alpha}\big(\frac1\nu u'(B_0)\big),\\ (u')^{-1}\big(\frac{1+\alpha}{1+\alpha\lambda}\nu\rho\big), & \rho>\frac{1+\alpha\lambda}{1+\alpha}\big(\frac1\nu u'(B_0)\big),\end{cases}$$
--   satisfies all of the following:
--   1. it exhausts the budget, $\mathbb E[\rho X^*_{\rm ex}(\lambda)]=x_0$;
--   2. it is optimal for (4);
--   3. every optimal solution of (4) equals it almost surely;
--   4. its optimal value $V_\lambda(X^*_{\rm ex}(\lambda)\mid B_0)$ is finite.
--
--   This is the benchmark with an exogenous reference point. Every later result in the mission is stated in terms of the optimal prospects $X^*_{\rm ex}(\Lambda)$ for various degrees of loss aversion $\Lambda$.
--
--   The prospect and its optimal value are jointly continuous in $(\lambda,\alpha)$. The Lean statement chooses a canonical formula (5) prospect for each parameter pair and states pointwise continuity almost surely and continuity of the real optimal value.
--
--   **Formalization Note.** Uniqueness is up to $P$-a.s. equality. Where $B_0=0$, $u'(B_0)=+\infty$ and the first case applies. Finiteness of the optimal value is stated in the proof (p. 32).
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 12 (PDF 12), Theorem 1, (4)–(5); finiteness from its proof, p. 32

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Theorem 1, p. 12: the optimal solution of (4) is unique (a.s.) and given by (5) with a
budget-exhausting multiplier `ν > 0`. A canonical family of these optima and its value are
jointly continuous in `(λ, α)`; the optimal value is finite (proof, p. 32). -/
theorem theorem_1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    (∃ ν : ℝ, 0 < ν ∧ price P ρ (Xhat ρ α u B0 ν lam) = ENNReal.ofReal x0 ∧
      IsOptEx P ρ x0 α u u0 B0 lam (Xhat ρ α u B0 ν lam) ∧
      (∀ X : Ω → ℝ, IsOptEx P ρ x0 α u u0 B0 lam X → X =ᵐ[P] Xhat ρ α u B0 ν lam) ∧
      V P α u u0 lam (Xhat ρ α u B0 ν lam) B0 ≠ ⊥) ∧
    (∃ νFamily : ℝ × ℝ → ℝ,
      (∀ p : ℝ × ℝ, 1 ≤ p.1 → 0 < p.2 →
        0 < νFamily p ∧
        price P ρ (Xhat ρ p.2 u B0 (νFamily p) p.1) = ENNReal.ofReal x0 ∧
        IsOptEx P ρ x0 p.2 u u0 B0 p.1 (Xhat ρ p.2 u B0 (νFamily p) p.1) ∧
        V P p.2 u u0 p.1 (Xhat ρ p.2 u B0 (νFamily p) p.1) B0 ≠ ⊥) ∧
      (∀ᵐ ω ∂P, ContinuousOn
        (fun p : ℝ × ℝ => Xhat ρ p.2 u B0 (νFamily p) p.1 ω)
        {p : ℝ × ℝ | 1 ≤ p.1 ∧ 0 < p.2}) ∧
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (V P p.2 u u0 p.1 (Xhat ρ p.2 u B0 (νFamily p) p.1) B0).toReal)
        {p : ℝ × ℝ | 1 ≤ p.1 ∧ 0 < p.2}) := by sorry

end EndoRefLA.PartialPPE
