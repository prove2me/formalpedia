-- Prove2me | Theorems.Thm_ESAxioms_Characterization_lemma_A7
-- name    : ESAxioms.Characterization.lemma_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:38.963987+00:00
-- url     : https://prove2.me/theorems/d7e776e3-d5c1-491e-9475-8ef51253560c
-- title:
--   Lemma A.7, p. 32 — for ℙ(A) = 1 − p, ESₚ(X) = 𝔼[X|A] iff A is a p-tail event of X
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$ and $X\in L^1$. For every event $A$ with $\mathbb P(A)=1-p$,
--   $$\mathrm{ES}_p(X)=\mathbb E[X\mid A]\iff A\text{ is a }p\text{-tail event of }X,$$
--   where $\mathbb E[X\mid A]=\mathbb E[X\mathbf 1_A]/\mathbb P(A)$.
--
--   The lemma characterizes exactly when the expected shortfall is attained as an average over an event of probability $1-p$.
--
--   **Formalization Note** $\mathrm{ES}_p$ is defined by the quantile integral, not through tail events, so the lemma is not definitional. $\mathbb E[X\mid A]$ is the elementary conditional expectation on an event, not Mathlib's σ-algebra `condExp`.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 32, Lemma A.7

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem lemma_A7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) (A : Set Ω) (hA : MeasurableSet A) (hPA : P.real A = 1 - p) :
    ES P p X = condExpOn P X A ↔ IsPTailEvent P p X A := by sorry

end ESAxioms.Characterization
