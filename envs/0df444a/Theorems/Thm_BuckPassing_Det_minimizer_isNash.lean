-- Prove2me | Theorems.Thm_BuckPassing_Det_minimizer_isNash
-- name    : BuckPassing.Det.minimizer_isNash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:10.475629+00:00
-- url     : https://prove2.me/theorems/447b4abd-eeeb-4230-b1f3-e3a230f94a03
-- title:
--   §3.1, p. 8 — component-wise minimizers of generalized ordinal potentials are Nash equilibria
-- statement:
--   Consider a cost game with players $i$, strategy sets $X_i$, cost functions $c_i$, and a generalized ordinal potential $\Psi$. If a profile $s$ minimizes $\Psi$ against every unilateral change, then $s$ is a pure Nash equilibrium:
--
--   $$\bigl[\forall i,\,x\in X_i,\quad \Psi(s)\leq\Psi(x,s_{-i})\bigr]\quad\Longrightarrow\quad \bigl[\forall i,\,x\in X_i,\quad c_i(s)\leq c_i(x,s_{-i})\bigr].$$
--
--   This observation connects minimization of a potential to the equilibrium condition and is used for the buck-passing game.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, p. 8, §3.1, sentence beginning 'It is also easy to see that a component-wise minimizer'

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

/-- §3.1, p. 8: a component-wise minimizer of a generalized ordinal potential is Nash. -/
theorem minimizer_isNash {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (s : ∀ i, X i) (hpot : IsGenOrdPotential c Ψ)
    (hmin : ∀ i (x : X i), Ψ s ≤ Ψ (Function.update s i x)) :
    IsNash c s := by sorry

end BuckPassing.Det
