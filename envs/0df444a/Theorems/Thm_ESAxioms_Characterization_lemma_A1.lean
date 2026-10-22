-- Prove2me | Theorems.Thm_ESAxioms_Characterization_lemma_A1
-- name    : ESAxioms.Characterization.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:51.262794+00:00
-- url     : https://prove2.me/theorems/8a886b83-6a3a-4ebe-ad70-3ca4c986c9d1
-- title:
--   Lemma A.1, p. 19 — a monotone, additive, law-invariant ρ on L¹₊ is λ𝔼 with λ ⩾ 0
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $L^1_+$ the non-negative integrable random variables. A functional $\rho:L^1_+\to\mathbb R$ is monotone, additive and law invariant if and only if there is $\lambda\ge 0$ with
--   $$\rho(X)=\lambda\,\mathbb E[X]\qquad\text{for all }X\in L^1_+ .$$
--
--   The lemma is the linear building block of Lemma A.2.
--
--   **Formalization Note** Atomlessness (the paper's standing assumption) is kept: on a space with atoms of different masses, evaluation at an atom is monotone, additive and law invariant but not a multiple of $\mathbb E$.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 19, Lemma A.1

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem lemma_A1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) :
    (AxiomM (L1Plus P) ρ ∧ IsAdditiveOn (L1Plus P) ρ ∧ AxiomLI P (L1Plus P) ρ) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ X ∈ L1Plus P, ρ X = c * ∫ ω, X ω ∂P := by sorry

end ESAxioms.Characterization
