-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_certificate_of_blossomSequence
-- name    : EdmondsMatching65.Polyhedron.certificate_of_blossomSequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:44:47.329976+00:00
-- url     : https://prove2.me/theorems/b3165c2c-ac40-4676-894f-9bb5ed8b703a
-- title:
--   §5, pp. 127–128 — a sequence {G_i} for M yields ⟨y, z⟩₀ satisfying (6)–(10)
-- statement:
--   Let $G$ be a finite graph with edge weights $c$ and let $M$ be a matching. If there exists a sequence $\{G_i\}_{i=0}^n$ satisfying conditions (a)–(k) of Theorem (M) for $G$, $c$ and $M$, then there is a dual vector $\langle y,z\rangle$ satisfying (6) and (7) and, relative to $M$, the conditions (8), (9) and (10).
--
--   This is the translation of §5: the paper builds $\langle y,z\rangle_0$ explicitly by $d_i=w(q^i)-w(u^{i+1})$ on the node sets $S_i$ absorbed into $u^{i+1}$ (11), $z=2d$ (12) and $y_v=w(v)-\sum_{S\ni v}d_S$ (13). It is the "if" direction of Theorem (M) in certificate form.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), pp. 127–128, §5, (11)–(16) and the verification of (6)–(10)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram
import Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence

namespace EdmondsMatching65.Polyhedron

theorem certificate_of_blossomSequence {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) (M : Finset E)
    (hM : IsMatching G M) (s : BlossomSequence G c M) :
    ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by sorry

end EdmondsMatching65.Polyhedron
