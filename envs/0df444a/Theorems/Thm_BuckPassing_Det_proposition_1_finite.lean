-- Prove2me | Theorems.Thm_BuckPassing_Det_proposition_1_finite
-- name    : BuckPassing.Det.proposition_1_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:17.290281+00:00
-- url     : https://prove2.me/theorems/64f7bd3d-db1f-4518-8c45-639b037bbdac
-- title:
--   Proposition 1, p. 8 — finite generalized ordinal potential games have a pure Nash equilibrium
-- statement:
--   Let the player set be finite and let every player have a finite, nonempty strategy set. If the cost game admits a generalized ordinal potential $\Psi$, then it has a pure Nash equilibrium:
--
--   $$\exists s\in\prod_i X_i\quad\forall i,\,x\in X_i,\qquad c_i(s)\leq c_i(x,s_{-i}).$$
--
--   This is the finite alternative of Proposition 1, used when the buck-passing strategies are out-neighbors of a finite graph.
--
--   **Formalization Note** Nonempty strategy sets are explicit: without them, a profile need not exist. This assumption is implicit in the paper's use of games with profiles.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, p. 8, Proposition 1 (finite alternative)

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

/-- Proposition 1, finite case: finite generalized ordinal potential games have a pure NE. -/
theorem proposition_1_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (hpot : IsGenOrdPotential c Ψ) :
    ∃ s : ∀ i, X i, IsNash c s := by sorry

end BuckPassing.Det
