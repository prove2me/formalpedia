-- Prove2me | Theorems.Thm_DiscreteChoiceProx_Simplex_lemma_2
-- name    : DiscreteChoiceProx.Simplex.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:37.600986+00:00
-- url     : https://prove2.me/theorems/e4d635b7-2942-4b59-a215-423c3b49be5f
-- title:
--   Lemma 2 — strong convexity and smoothness duality
-- statement:
--   For a positive parameter $\beta$, the conjugate $E^*$ is $\beta$-strongly convex on $\Delta$ in the $\ell_1$ norm exactly when the surplus $E$ is $1/\beta$-strongly smooth in the dual maximum norm:
--
--   $$
--   E^*\text{ is }\beta\text{-strongly convex in }\ell_1
--   \quad\Longleftrightarrow\quad
--   E\text{ is }\frac1\beta\text{-strongly smooth in }\ell_\infty.
--   $$
--
--   The statement keeps both directions of the paper's duality lemma. It transfers a smoothness estimate for the surplus into the convexity assertion about its conjugate.
--
--   **Formalization Note** Assumption 1 ensures $E^*$ is finite on $\Delta$; the real-valued restriction is interpreted through that result. The smoothness predicate uses Mathlib's sup norm on finite coordinate functions.
-- source:
--   Müller, Nesterov, Shikhman, Discrete choice prox-functions on the simplex, arXiv:1909.05591v1, p. 7, Lemma 2

import Mathlib
import Definitions.Def_DiscreteChoiceProx_Simplex_Model

open MeasureTheory

namespace DiscreteChoiceProx.Simplex

/-- Lemma 2, p. 7: duality of strong convexity and strong smoothness. -/
theorem lemma_2 {n : ℕ} [NeZero n] (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hA : Assumption1 μ) (β : ℝ) (hβ : 0 < β) :
    IsStronglyConvexL1 (fun p => (conj μ p).toReal) β ↔
      IsStronglySmoothSup (surplus μ) (1 / β) := by sorry

end DiscreteChoiceProx.Simplex
