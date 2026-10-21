-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_theorem_2
-- name    : EndoRefLA.PartialPPE.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:45.352418+00:00
-- url     : https://prove2.me/theorems/12b7c29a-366d-4cc0-8dea-53ee672671f8
-- title:
--   Theorem 2, p. 15 — PEs are the budget-exhausting prospects satisfying (7); the PPE is X*_en = (u′)⁻¹(νρ) of (8)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Consider the fully endogenous model: a prospect $X\in\mathcal X(x_0)$ is a personal equilibrium (PE) if $V_\lambda(X\mid X)\ge V_\lambda(Y\mid X)$ for all $Y\in\mathcal X(x_0)$, and a preferred personal equilibrium (PPE) if moreover $V_\lambda(X\mid X)\ge V_\lambda(Z\mid Z)$ for every PE $Z$.
--
--   1. Let $X\in\mathcal X(x_0)$. $X$ is a PE if and only if $\mathbb E[\rho X]=x_0$ and there is $\nu>0$ with
--   $$(u')^{-1}\Big(\frac{\nu\rho}{1+\alpha}\Big)\le X\le(u')^{-1}\Big(\frac{\nu\rho}{1+\alpha\lambda}\Big)\quad\text{a.s.}$$
--   2. There is $\nu>0$ with $\mathbb E[\rho(u')^{-1}(\nu\rho)]=x_0$.
--   3. For any such $\nu$, a prospect $X\in\mathcal X(x_0)$ is a PPE if and only if $X=X^*_{\rm en}:=(u')^{-1}(\nu\rho)$ a.s.
--
--   With a fully endogenous reference point and state-dependent evaluation, loss aversion has no effect on the preferred choice: the PPE is the classical expected-utility optimum.
--
--   **Formalization Note.** The printed theorem omits the budget equality $\mathbb E[\rho X]=x_0$ from the PE characterization. Without it the statement is false (for $\lambda=1$, every $\nu$ whose budget is at most $x_0$ satisfies (7)). The proof (p. 33) applies Theorem 1, whose multiplier exhausts the budget, so the equality is added here. A PE candidate must also be an admissible reference point, $\mathbb E|u(X)|<\infty$ (standing restriction, p. 9). Under (7) this holds automatically by Assumption 1.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 15 (PDF 15), Theorem 2, (7)–(8); budget equality from the proof, p. 33

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Theorem 2, p. 15, with the budget equality `E[ρX] = x0` of its proof (p. 33) made explicit
in the PE characterization (7); and the PPE (8). -/
theorem theorem_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    (∀ X : Ω → ℝ, Feasible P ρ x0 X →
      (IsPEin P α u u0 lam {Y | Feasible P ρ x0 Y} X ↔
        price P ρ X = ENNReal.ofReal x0 ∧
          ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂P,
            Iinv u (ν * ρ ω / (1 + α)) ≤ X ω ∧ X ω ≤ Iinv u (ν * ρ ω / (1 + α * lam)))) ∧
    (∃ ν : ℝ, 0 < ν ∧ price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0) ∧
    (∀ ν : ℝ, 0 < ν → price P ρ (fun ω => Iinv u (ν * ρ ω)) = ENNReal.ofReal x0 →
      ∀ X : Ω → ℝ, Feasible P ρ x0 X →
        (IsPPEin P α u u0 lam {Y | Feasible P ρ x0 Y} X ↔
          X =ᵐ[P] fun ω => Iinv u (ν * ρ ω))) := by sorry

end EndoRefLA.PartialPPE
