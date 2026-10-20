-- Prove2me | Theorems.Thm_BuckPassing_Det_proposition_1_compact
-- name    : BuckPassing.Det.proposition_1_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:12.187043+00:00
-- url     : https://prove2.me/theorems/6ec35616-ce60-47b2-ba22-9a3c3cf2c248
-- title:
--   Proposition 1, p. 8 — compact generalized ordinal potential games have a pure Nash equilibrium
-- statement:
--   Let the player set be finite and each strategy set $X_i$ be nonempty and compact. If $\Psi$ is a lower semicontinuous generalized ordinal potential for a cost game, then the game has a pure Nash equilibrium:
--
--   $$\exists s\in\prod_i X_i\quad\forall i,\,x\in X_i,\qquad c_i(s)\leq c_i(x,s_{-i}).$$
--
--   This is the compact alternative of Proposition 1; it applies to games with continuous strategy sets when the potential has the stated regularity.
--
--   **Formalization Note** Nonempty strategy sets are explicit because compactness alone permits the empty set. The finite player set supplies the finite product topology used for the potential.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, p. 8, Proposition 1 (compact alternative)

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

/-- Proposition 1, compact case: a lower semicontinuous potential attains a Nash minimum. -/
theorem proposition_1_compact {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (hpot : IsGenOrdPotential c Ψ) (hlsc : LowerSemicontinuous Ψ) :
    ∃ s : ∀ i, X i, IsNash c s := by sorry

end BuckPassing.Det
