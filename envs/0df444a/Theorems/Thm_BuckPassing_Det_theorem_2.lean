-- Prove2me | Theorems.Thm_BuckPassing_Det_theorem_2
-- name    : BuckPassing.Det.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:28.118859+00:00
-- url     : https://prove2.me/theorems/a699bc9c-7932-4838-b8e5-1195fb703da3
-- title:
--   Theorem 2, p. 10 — every deterministic buck-passing game has a prior-free Nash equilibrium
-- statement:
--   Let $G=(V,E)$ be a finite directed graph without loops, with at least one out-neighbor at every vertex. Every player chooses one out-neighbor once and for all. There is a single strategy profile $s$ that is a pure Nash equilibrium for the long-run buck-holding costs under every initial probability distribution $\mu$:
--
--   $$\exists s\in\prod_{i\in V}N_i^+\quad\forall\mu\in\Delta(V),\quad\forall i\in V,\ \forall x\in N_i^+,\qquad c_i(s)\leq c_i(x,s_{-i}).$$
--
--   The profile is prior-free because its choice does not depend on $\mu$. This is the main existence result for the deterministic game.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, p. 10, Theorem 2

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

/-- Theorem 2: one profile is Nash for every initial probability distribution. -/
theorem theorem_2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) :
    ∃ s : ∀ i, Strat G i, IsPFNE G s := by sorry

end BuckPassing.Det
