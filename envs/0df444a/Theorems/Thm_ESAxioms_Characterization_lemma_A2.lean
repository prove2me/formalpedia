-- Prove2me | Theorems.Thm_ESAxioms_Characterization_lemma_A2
-- name    : ESAxioms.Characterization.lemma_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:09.467781+00:00
-- url     : https://prove2.me/theorems/b49d91ff-d514-44a7-abff-e32450363b7e
-- title:
--   Lemma A.2, p. 20 — a monotone ρ on L¹ is law invariant and p-additive iff ρ = a𝔼 + bESₚ
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $\rho:L^1\to\mathbb R$ be monotone. Then $\rho$ is law invariant and $p$-additive if and only if there are $a,b\in\mathbb R$ with
--   $$\rho(X)=a\,\mathbb E[X]+b\,\mathrm{ES}_p(X)\qquad\text{for all }X\in L^1 .$$
--
--   This is the pivotal lemma of the paper: together with Proposition 4 it reduces Theorem 1 to determining $a$ and $b$.
--
--   **Formalization Note** Monotonicity (sure order) is a hypothesis of both directions, as on the page; $a$ and $b$ are unrestricted reals.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 20, Lemma A.2

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem lemma_A2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (ρ : (Ω → ℝ) → ℝ) (hM : AxiomM (L1 P) ρ) :
    (AxiomLI P (L1 P) ρ ∧ IsPAdditive P p (L1 P) ρ) ↔
      ∃ a b : ℝ, ∀ X ∈ L1 P, ρ X = a * ∫ ω, X ω ∂P + b * ES P p X := by sorry

end ESAxioms.Characterization
