-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_separateness_extends
-- name    : EnsembleSpaceDraft.separateness_extends
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:50:27.616605+00:00
-- url     : https://prove2.me/theorems/2b1a0872-526c-4f6d-9066-b041d682d522
-- title:
--   Proposition 1.27 — separateness extends to all mixtures
-- statement:
--   Let $e,e_1,e_2$ be ensembles and let $p\in(0,1)$. If $e$ is separate from the mixture $p e_1+\bar p e_2$, then $e$ is separate from $\lambda e_1+\bar\lambda e_2$ for every coefficient $\lambda\in[0,1]$.
--
--   In particular $e$ is separate from $e_1$ and from $e_2$. Separateness from one nontrivial mixture of a pair spreads to the whole segment joining that pair.
--
--   This is Proposition 1.27. The hypothesis is existential in $p$ (some coefficient in the open interval) and the conclusion is universal in $\lambda$ (every coefficient in the closed interval).
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Proposition 1.27, pp. 23–24.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

/-- Proposition 1.27. Separateness from one nontrivial mixture extends to every mixture
of the same two ensembles, including the endpoints. -/
theorem separateness_extends {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (e e₁ e₂ : E) (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : X.Separate e (X.mix p e₁ e₂)) :
    ∀ q : unitInterval, X.Separate e (X.mix q e₁ e₂) := by
  sorry

end EnsembleSpaceDraft
