-- Prove2me | Theorems.Thm_ESAxioms_Characterization_proposition_1
-- name    : ESAxioms.Characterization.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:52.592989+00:00
-- url     : https://prove2.me/theorems/46e79308-7b0c-4347-974c-4a18cfbc4ab6
-- title:
--   Proposition 1, p. 10 — ESₚ and VaRₚ satisfy Axioms M, LI and P on L¹
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $p\in(0,1)$. On the domain $\mathcal X=L^1$, both functionals $\mathrm{ES}_p$ and $\mathrm{VaR}_p$ satisfy
--
--   1. Axiom M (monotonicity in the sure order),
--   2. Axiom LI (law invariance), and
--   3. Axiom P (prudence: $\lim_k\rho(\xi_k)\ge\rho(X)$ whenever $\xi_k\to X$ pointwise in $L^1$ and the limit exists).
--
--   It supplies the first three axioms for the "if" direction of Theorem 1.
--
--   **Formalization Note** Six conjuncts on the domain $L^1$. No atomlessness is assumed.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 10, Proposition 1

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (AxiomM (L1 P) (ES P p) ∧ AxiomLI P (L1 P) (ES P p) ∧ AxiomP (L1 P) (ES P p)) ∧
    (AxiomM (L1 P) (VaR P p) ∧ AxiomLI P (L1 P) (VaR P p) ∧ AxiomP (L1 P) (VaR P p)) := by sorry

end ESAxioms.Characterization
