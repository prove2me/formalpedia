-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_problem_10_iff_16
-- name    : EndoRefLA.PartialPPE.problem_10_iff_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:58.135908+00:00
-- url     : https://prove2.me/theorems/a89f8d4b-5fc6-4270-9fe3-40ced69ece63
-- title:
--   Proof of Theorem 3, p. 33 — when (16) has an optimum, the partially endogenous PPEs are exactly the optima of (16)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Let $f:\mathbb R\to\mathbb R$ be a mental cost function and $c_0\in\mathbb R$, and let
--   $$\mathcal Y(B_0,c_0)=\{X\in\mathcal X(x_0): f(V_\lambda(X\mid B_0))\le c_0\}.$$
--   A partially endogenous PPE given $\mathcal Y(B_0,c_0)$ (problem (10)) is a PE within $\mathcal Y(B_0,c_0)$ that maximizes $V_\lambda(X\mid X)$ among such PEs.
--
--   Problem (16) maximizes $V_\lambda(X\mid X)$ over $X\in\mathcal Y(B_0,c_0)$. Suppose (16) has an optimal solution. Then, for every $X$,
--   $$X\text{ is a partially endogenous PPE given }\mathcal Y(B_0,c_0)\iff X\in\mathcal Y(B_0,c_0)\text{ and }V_\lambda(Y\mid Y)\le V_\lambda(X\mid X)\ \ \forall Y\in\mathcal Y(B_0,c_0).$$
--
--   This reduces the equilibrium problem (10) to the single optimization problem (16). The paper takes the reduction from Proposition 6 of De Giorgi and Post (2011).
--
--   **Formalization Note.** The existence of an optimum of (16) is a hypothesis; the paper applies the equivalence only where it holds. No property of $f$ is needed. Prospects with $V_\lambda(X\mid B_0)=-\infty$ are excluded from $\mathcal Y(B_0,c_0)$ (domain convention for $f_{B_0}$), so every element of $\mathcal Y(B_0,c_0)$ has $\mathbb E|u(X)|<\infty$.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 33 (PDF 33), proof of Theorem 3, problems (10) and (16)

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 3, p. 33 (Proposition 6 of De Giorgi and Post, 2011): when problem (16) has
an optimal solution, the partially endogenous PPEs given `Y(B0, c0)` (problem (10)) are exactly
the optimal solutions of (16). -/
theorem problem_10_iff_16
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (f : ℝ → ℝ) (c0 : ℝ)
    (hmax : ∃ Xs ∈ Ycal P ρ x0 α u u0 lam B0 f c0, ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam Xs Xs) :
    ∀ X : Ω → ℝ, IsPPEin P α u u0 lam (Ycal P ρ x0 α u u0 lam B0 f c0) X ↔
      (X ∈ Ycal P ρ x0 α u u0 lam B0 f c0 ∧ ∀ Y ∈ Ycal P ρ x0 α u u0 lam B0 f c0, V P α u u0 lam Y Y ≤ V P α u u0 lam X X) := by sorry

end EndoRefLA.PartialPPE
