-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_balanced_vertex_elimination
-- name    : AnonymousDirectedCounting.Exact.Supplement.balanced_vertex_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:09.190017+00:00
-- url     : https://prove2.me/theorems/5f9a5b21-9ac4-4730-a0b0-bd2869f7f0fa
-- title:
--   Lemma 10 — eliminating a balanced auxiliary vertex
-- statement:
--   Let $D$ be a directed multigraph on $V\cup\{z\}$ with $V$ finite and nonempty. Suppose that every ordered pair of vertices of $V$ is joined by a directed path of $D$, that $z$ has no loop, and that
--   $$d^-(z)=d^+(z).$$
--   Then the arcs at $z$ can be paired, each arc $a\to z$ with an arc $z\to b$, so that replacing every pair $a\to z\to b$ by an arc $a\to b$ (keeping all other arcs) leaves a strongly connected multigraph on $V$.
--
--   The lemma turns a balanced auxiliary routing vertex into direct arcs without losing strong connectivity; it is the step that converts certificate tables into actual round graphs.
--
--   Differences from the source:
--   - encoding: a directed multigraph on V ∪ {z} → arc multiplicities D on Option V with z = none; reason: same object
--   - encoding: a pairing of the arcs into z with the arcs out of z → a matrix P with row sums D(a, z) and column sums D(z, b), P a b counting the pairs a → z → b; reason: parallel arc copies are interchangeable, every pairing gives such a matrix and every such matrix arises from a pairing
--   - encoding: joined by a directed path / strongly connected → Relation.ReflTransGen of positive multiplicity, for every ordered pair; reason: the definition of strong connectivity by paths
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 25 (PDF p. 27), Lemma 10

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Rounds

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 10, printed p. 25 (PDF p. 27). `D` is a directed multigraph on `V ∪ {z}`, written on
`Option V` with `z = none`; `V` is finite and nonempty. If every ordered pair of vertices of `V` is
joined by a directed path of `D`, `z` has no loop, and `d⁻(z) = d⁺(z)`, then the arcs at `z` can be
paired — a pairing is recorded by the number `P a b` of pairs `a → z → b`, whose row and column sums
are the numbers of arcs `a → z` and `z → b` — so that replacing each pair by an arc `a → b` leaves a
strongly connected multigraph on `V`. -/
theorem balanced_vertex_elimination {V : Type} [Fintype V] [Nonempty V]
    (D : Option V → Option V → ℕ)
    (hpath : ∀ x y : V, Relation.ReflTransGen (fun a b => 0 < D a b) (some x) (some y))
    (hloop : D none none = 0)
    (hbal : ∑ a, D a none = ∑ b, D none b) :
    ∃ P : V → V → ℕ, (∀ a, ∑ b, P a b = D (some a) none) ∧
      (∀ b, ∑ a, P a b = D none (some b)) ∧
      PathConnected (fun x y : V => 0 < D (some x) (some y) + P x y) := by sorry

end AnonymousDirectedCounting.Exact.Supplement
