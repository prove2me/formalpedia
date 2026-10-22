-- Prove2me | Theorems.Thm_ESAxioms_Characterization_lemma_A5
-- name    : ESAxioms.Characterization.lemma_A5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:38.274034+00:00
-- url     : https://prove2.me/theorems/62a2d76b-e45d-49c1-9595-02afe3a82b8e
-- title:
--   Lemma A.5, p. 28 — for a p-concentrated pair (X, Y), the p-tail events of X + Y are exactly the common p-tail events of X and Y
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $(X,Y)$ be a $p$-concentrated pair of random variables, i.e. $X$ and $Y$ have a common tail event of probability $1-p$. Then for every event $A$,
--   $$A \text{ is a } p\text{-tail event of } X+Y \iff A \text{ is a } p\text{-tail event of both } X \text{ and } Y .$$
--
--   This is the key step relating the tail events of an aggregate loss to those of its components, used for Theorem 5.
--
--   **Formalization Note** The pair is written `![X, Y]`; $X$ and $Y$ are assumed measurable.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 28, Lemma A.5

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem lemma_A5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IsPConcentrated P p ![X, Y])
    (A : Set Ω) :
    IsPTailEvent P p (X + Y) A ↔ (IsPTailEvent P p X A ∧ IsPTailEvent P p Y A) := by sorry

end ESAxioms.Characterization
