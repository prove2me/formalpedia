-- Prove2me | Theorems.Thm_ESAxioms_Characterization_proposition_4
-- name    : ESAxioms.Characterization.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:59.001552+00:00
-- url     : https://prove2.me/theorems/df025276-3f32-4bce-983a-16ec29c97e52
-- title:
--   Proposition 4, p. 11 — under Axiom LI on L^q, NRC holds iff ρ is p-additive for some p ∈ (0,1), with p = 1 − ℙ(A) (proof, p. 25)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $q\in[0,\infty]$, and let $\rho:L^q\to\mathbb R$ satisfy Axiom LI. Then
--
--   1. $\rho$ satisfies Axiom NRC if and only if, for some $p\in(0,1)$, $\rho$ is $p$-additive:
--   $$\rho(X+Y)=\rho(X)+\rho(Y)\quad\text{for all }X,Y\in L^q\text{ sharing a tail event of probability }1-p;$$
--   2. more precisely, if $A$ is a stress event of Axiom NRC, then $\rho$ is $(1-\mathbb P(A))$-additive.
--
--   Under law invariance, the no-reward-for-concentration axiom is therefore the functional property of $p$-additivity, with $p$ determined by the probability of the stress event.
--
--   **Formalization Note** Part 2 is the value of $p$ exhibited in the paper's proof of the forward direction ("Suppose that ρ satisfies Axiom NRC with A being the stress event, and let p = 1−ℙ(A)", p. 25), which the proof of Theorem 1 quotes (p. 22). $L^q$ is "measurable with `MemLp X q P`", so $q=0$ gives $L^0$ and $q=\infty$ gives $L^\infty$. A stress event has $0<\mathbb P(A)<1$ (see the definitions item).
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 11, Proposition 4, and its proof, pp. 25–26

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem proposition_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (q : ENNReal)
    (ρ : (Ω → ℝ) → ℝ) (hLI : AxiomLI P (Lq P q) ρ) :
    (AxiomNRC P (Lq P q) ρ ↔ ∃ p ∈ Set.Ioo (0 : ℝ) 1, IsPAdditive P p (Lq P q) ρ) ∧
    ∀ A : Set Ω, IsStressEvent P (Lq P q) ρ A → IsPAdditive P (1 - P.real A) (Lq P q) ρ := by sorry

end ESAxioms.Characterization
