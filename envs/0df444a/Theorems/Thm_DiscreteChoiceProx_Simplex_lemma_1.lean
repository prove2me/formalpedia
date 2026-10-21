-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_lemma_1
-- name    : DiscreteChoiceProx.Simplex.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:26.650315+00:00
-- url     : https://prove2.me/theorems/11e2ccee-6994-409e-beea-55c973399308
-- title:
--   Lemma 1 — elementary properties of the surplus
-- statement:
--   For the surplus $E$ of an additive random utility model satisfying Assumption 1, let $\mathbf1$ be the all-ones utility vector and $m_i=\mathbb E_\mu[\epsilon_i]$. Then:
--
--   $$
--   E(u+\gamma\mathbf1)=E(u)+\gamma,\qquad
--   u\ge v\Longrightarrow E(u)\ge E(v),\qquad
--   E(u)\ge\max_i u_i+\min_i m_i.
--   $$
--
--   The three claims are the paper's (E1), (E2) and (E3). They control translation, monotonicity and a finite lower bound on the surplus, respectively. In particular, they underlie the domain calculation for $E^*$.
--
--   **Formalization Note** The finite-mean condition is the coordinate-integrability clause of Assumption 1. The index type is nonempty.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 5, Lemma 1

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Lemma 1 (E1)–(E3), p. 5. -/
theorem lemma_1 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ) :
    (∀ (u : Fin n → ℝ) (γ : ℝ),
      surplus μ (u + fun _ => γ) = surplus μ u + γ) ∧
    (∀ u v : Fin n → ℝ, (∀ i, v i ≤ u i) → surplus μ v ≤ surplus μ u) ∧
    (∀ u : Fin n → ℝ,
      (Finset.univ.sup' Finset.univ_nonempty fun i => u i) +
        (Finset.univ.inf' Finset.univ_nonempty fun i => ∫ e, e i ∂μ) ≤ surplus μ u) := by sorry

end DiscreteChoiceProx.Simplex
