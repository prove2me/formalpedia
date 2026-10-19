-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_boundedAround_iff_tendsto
-- name    : EnsembleSpaceDraft.boundedAround_iff_tendsto
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:48:49.244353+00:00
-- url     : https://prove2.me/theorems/daaf12d5-45f5-44f5-b870-4616b71b9f21
-- title:
--   Proposition 1.17 — sequential characterization of boundedness
-- statement:
--   Let $A$ be a set of ensembles and let $e$ be an ensemble. Then $A$ is bounded around $e$ if and only if the following sequential condition holds. For every sequence of coefficients $p_n\in[0,1]$ with $p_n\to 1$, and every sequence $a_n\in A$,
--   $$
--   p_n e+\bar p_n a_n\to e.
--   $$
--   Boundedness around $e$ is Definition 1.16: every open neighbourhood of $e$ contains $pe+\bar p A$ for some $p\in[0,1)$.
--
--   This is Proposition 1.17. No metric, no vector-space structure, and no entropy are assumed.
--
--   **Formalization Note.** Convergence is convergence in the given topology. The coefficients $p_n$ are unit-interval elements, so the sequence cannot leave $[0,1]$.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Definition 1.16 and Proposition 1.17, pp. 17–19.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval
open Filter Topology

namespace EnsembleSpaceDraft

universe u

/-- Proposition 1.17. `A` is bounded around `e` if and only if `pₙ e + (1 - pₙ) aₙ → e`
whenever `pₙ → 1` and `aₙ ∈ A`. -/
theorem boundedAround_iff_tendsto {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (A : Set E) (e : E) :
    X.BoundedAround A e ↔
      ∀ (p : ℕ → unitInterval) (a : ℕ → E),
        (∀ n, a n ∈ A) → Tendsto (fun n => (p n : ℝ)) atTop (nhds 1) →
          Tendsto (fun n => X.mix (p n) e (a n)) atTop (nhds e) := by
  sorry

end EnsembleSpaceDraft
