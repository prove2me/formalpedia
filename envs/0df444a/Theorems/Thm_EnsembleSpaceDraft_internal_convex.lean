-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_internal_convex
-- name    : EnsembleSpaceDraft.internal_convex
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:49:21.890849+00:00
-- url     : https://prove2.me/theorems/2f5eea65-4923-46aa-a9c8-ed5627e938d8
-- title:
--   Proposition 1.21 — internal points form a convex set
-- statement:
--   Let $e_1$ and $e_2$ be internal points of an ensemble space, and let $p\in[0,1]$. The mixture $p e_1+\bar p e_2$ is again internal.
--
--   Equivalently, the set of internal points is a convex subset: it contains every finite mixture of its members, since a binary mixture stays inside the set and finite mixtures are iterated binary mixtures.
--
--   An internal point is an ensemble that admits every ensemble as a component (Definition 1.20). This is Proposition 1.21. The set of internal points may be empty; the statement does not claim otherwise.
--
--   **Formalization Note.** The witnessing coefficient in the definition of an internal point lies in $(0,1]$, including the endpoint $1$. The proof in the draft writes a strict inequality in one algebraic step; the statement formalized here is the definition and the claim as printed in Proposition 1.21, not the intermediate formula that divides by $1-\lambda$.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Definition 1.20 and Proposition 1.21, pp. 20–21.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

/-- Proposition 1.21. The set of internal points is convex. -/
theorem internal_convex {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (e₁ e₂ : E) (p : unitInterval) (h₁ : X.IsInternal e₁) (h₂ : X.IsInternal e₂) :
    X.IsInternal (X.mix p e₁ e₂) := by
  sorry

end EnsembleSpaceDraft
