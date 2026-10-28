-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_V_self_eq_Ex
-- name    : EndoRefLA.PartialPPE.V_self_eq_Ex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:46.520045+00:00
-- url     : https://prove2.me/theorems/bcd87042-7e3e-492c-b8fc-108e3d8973df
-- title:
--   Proof of Theorem 2, p. 33 — V_λ(X|X) = E[u(X)]
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   For every prospect $X$, the preference value of $X$ evaluated against itself is its expected consumption utility:
--   $$V_\lambda(X\mid X)=\mathbb E[u(X)].$$
--
--   The gain-loss term vanishes state by state, because the evaluation is state-dependent. This identity is what makes the PPE independent of loss aversion (Theorem 2) and reduces problem (16) to maximizing expected utility.
--
--   **Formalization Note.** It is stated for every $X$, including those with $\mathbb E[u(X)]=-\infty$ (both sides are then $-\infty$). The paper states it for $X\in\mathcal X(x_0)$.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 33 (PDF 33), proof of Theorem 2; also p. 17

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, p. 33: `V_λ(X|X) = E[u(X)]` (here for every `X`). -/
theorem V_self_eq_Ex
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0) :
    ∀ X : Ω → ℝ, V P α u u0 lam X X = Ex P (fun ω => uE u u0 (X ω)) := by sorry

end EndoRefLA.PartialPPE
