-- Prove2me | Theorems.Thm_ESAxioms_Characterization_lemma_A3
-- name    : ESAxioms.Characterization.lemma_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:32.206305+00:00
-- url     : https://prove2.me/theorems/3b656da3-97ca-49a0-b984-86d4e95a70f4
-- title:
--   Lemma A.3, p. 26 — A is a p-tail event of X iff ℙ(A) = 1 − p and {X > xₚ} ⊂ A ⊂ {X ⩾ xₚ} a.s.; a p-tail event always exists
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, $X$ a random variable and $x_p=\mathrm{VaR}_p(X)$. Then
--
--   1. an event $A$ is a $p$-tail event of $X$ if and only if
--   $$\mathbb P(A)=1-p\quad\text{and}\quad \{X>x_p\}\subset A\subset\{X\ge x_p\}\ \text{almost surely};$$
--   2. a $p$-tail event of $X$ always exists.
--
--   The lemma identifies $p$-tail events with the events of probability $1-p$ squeezed between the strict and weak upper level sets of $X$ at its left $p$-quantile.
--
--   **Formalization Note** "Almost surely" inclusions are `≤ᵐ[P]`. $X$ is assumed measurable; atomlessness is the paper's standing assumption and is used for existence.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 26, Lemma A.3

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem lemma_A3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : Measurable X) :
    (∀ A : Set Ω, MeasurableSet A →
      (IsPTailEvent P p X A ↔
        (P.real A = 1 - p ∧ {ω | VaR P p X < X ω} ≤ᵐ[P] A ∧ A ≤ᵐ[P] {ω | VaR P p X ≤ X ω}))) ∧
    ∃ A : Set Ω, IsPTailEvent P p X A := by sorry

end ESAxioms.Characterization
