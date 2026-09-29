-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_lattice
-- name    : AssignmentGame.CoreCorners.core_lattice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:24:07.545528+00:00
-- url     : https://prove2.me/theorems/f6bc491c-cc89-45ca-b51e-a7a7e90b5e6b
-- title:
--   Lemma (p. 121) — coordinatewise min/max of two core vectors, paired oppositely, are in the core
-- statement:
--   Let $M$ (sellers) and $N$ (buyers) be finite sets and $a_{ij} \ge 0$. Let $(u', v')$ and $(u'', v'')$ be two payoff vectors in the core, and define, for $i \in M$ and $j \in N$,
--   $$\underline u_i = \min(u'_i, u''_i), \quad \underline v_j = \min(v'_j, v''_j), \quad \overline u_i = \max(u'_i, u''_i), \quad \overline v_j = \max(v'_j, v''_j).$$
--   Then both
--   $$(\underline u, \overline v) \quad \text{and} \quad (\overline u, \underline v)$$
--   are in the core.
--
--   This lattice property is the heart of Theorem 3: taking sellers' minima together with buyers' maxima (or the reverse) never leaves the core.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 121, Lemma

import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game

open Finset

namespace AssignmentGame.CoreCorners

/-- Lemma, p. 121: for two core vectors `(u', v')` and `(u'', v'')`, the vectors
`(min u' u'', max v' v'')` and `(max u' u'', min v' v'')` (taken coordinatewise) are in the
core. -/
theorem core_lattice {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (u' u'' : M → ℝ) (v' v'' : N → ℝ)
    (h' : (u', v') ∈ core a) (h'' : (u'', v'') ∈ core a) :
    ((fun i => min (u' i) (u'' i)), (fun j => max (v' j) (v'' j))) ∈ core a ∧
    ((fun i => max (u' i) (u'' i)), (fun j => min (v' j) (v'' j))) ∈ core a := by sorry

end AssignmentGame.CoreCorners
