-- Prove2me | Theorems.Thm_ESAxioms_Characterization_theorem_1
-- name    : ESAxioms.Characterization.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:19.432981+00:00
-- url     : https://prove2.me/theorems/5fd2364d-7e6d-415a-8a6e-3e4706b8b459
-- title:
--   Theorem 1, p. 9 — a normalized ρ on L¹ satisfies Axioms M, LI, P and NRC iff ρ = ESₚ for some p ∈ (0,1), with p = 1 − ℙ(A)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and let $\rho:L^1\to\mathbb R$ be a functional with $\rho(1)=1$. Then
--
--   1. $\rho$ satisfies Axioms M, LI, P and NRC if and only if there is $p\in(0,1)$ with
--   $$\rho(X)=\mathrm{ES}_p(X)=\frac{1}{1-p}\int_p^1\mathrm{VaR}_q(X)\,\mathrm dq\qquad\text{for all }X\in L^1;$$
--   2. in the forward direction, the value of $p$ is uniquely given by $p=1-\mathbb P(A)$, where $A$ is any stress event in Axiom NRC: if $\rho$ satisfies M, LI and P and $A$ is a stress event, then $\rho=\mathrm{ES}_{1-\mathbb P(A)}$ on $L^1$, and $\rho=\mathrm{ES}_p$ on $L^1$ forces $p=1-\mathbb P(A)$.
--
--   This is the main result of the paper: monotonicity, law invariance, prudence and no reward for concentration characterize the Expected Shortfall family, with no convexity, subadditivity or translation invariance assumed.
--
--   **Formalization Note** $\rho$ is a map on all functions $\Omega\to\mathbb R$, and "$\rho=\mathrm{ES}_p$" means equality on $L^1$. Axiom M uses the sure order and Axiom P pointwise convergence, as on p. 6. A stress event is required to satisfy $0<\mathbb P(A)<1$: without it $A=\emptyset$ satisfies NRC vacuously and $\mathrm{VaR}_p$ would be a counterexample (Proposition 1 and Example 1). The normalization is $\rho(1)=1$ for the constant random variable $1$.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 9, Theorem 1

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) (h1 : ρ (fun _ => 1) = 1) :
    ((AxiomM (L1 P) ρ ∧ AxiomLI P (L1 P) ρ ∧ AxiomP (L1 P) ρ ∧ AxiomNRC P (L1 P) ρ) ↔
        ∃ p ∈ Set.Ioo (0 : ℝ) 1, ∀ X ∈ L1 P, ρ X = ES P p X) ∧
    ((AxiomM (L1 P) ρ ∧ AxiomLI P (L1 P) ρ ∧ AxiomP (L1 P) ρ) →
        ∀ A : Set Ω, IsStressEvent P (L1 P) ρ A →
          (∀ X ∈ L1 P, ρ X = ES P (1 - P.real A) X) ∧
          ∀ p ∈ Set.Ioo (0 : ℝ) 1, (∀ X ∈ L1 P, ρ X = ES P p X) → p = 1 - P.real A) := by sorry

end ESAxioms.Characterization
