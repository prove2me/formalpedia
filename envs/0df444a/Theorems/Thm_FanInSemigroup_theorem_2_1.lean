-- Prove2me | Theorems.Thm_FanInSemigroup_theorem_2_1
-- name    : FanInSemigroup.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:46.677226+00:00
-- url     : https://prove2.me/theorems/c0b88f86-4534-4b14-94f1-c8db20587492
-- title:
--   Theorem 2.1 — a finite semigroup has constant-depth, polynomial-size circuits iff it is groupfree
-- statement:
--   Let $S$ be a finite semigroup and $e:S\to\{0,1\}^k$ an injective encoding of its elements. Then there are constant depth, polynomial size circuits computing $S$ under $e$, in the sense that there are $D,c$ such that for every $n\ge 1$ some circuit maps the encodings of $a_1,\dots,a_n$ to the encoding of $a_1a_2\cdots a_n$ with depth at most $D$ and size at most $c\,n^c$, if and only if
--
--   $$
--   S\text{ contains no nontrivial subgroup as a subset.}
--   $$
--
--   This is the paper's complete characterization of the associative functions computable by constant-depth, polynomial-size, unbounded fan-in circuits. In particular, whether such circuits exist does not depend on the encoding.
--
--   Differences from the source:
--   - reading: "an encoding ... using k bits is fixed" → the equivalence for every k and every injective encoding; reason: this covers both "some encoding" and "every encoding", and both directions of the proof work for any encoding
--   - reading: "circuits" with no uniformity stated → a non-uniform family, one circuit per n ≥ 1, with constants independent of n; reason: the page states no uniformity condition
--   - encoding: polynomial size → size ≤ c·n^c for n ≥ 1; reason: equivalent at n ≥ 1 to any polynomial bound
--   - encoding: a directed acyclic graph with input nodes labelled by variables → gates in topological order, one input node per variable; reason: merging input nodes with the same label only lowers the size; no instance changes
--   - encoding: "semigroup G", with "Throughout this section all semigroups are finite" → [Semigroup S] [Finite S]; reason: the standing assumption of the section; the empty semigroup is allowed, and both sides hold there
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Theorem 2.1, p.54

import Definitions.Def_FanInSemigroup_HasConstDepthPolySize
import Definitions.Def_FanInSemigroup_IsGroupfree

set_option autoImplicit false

namespace FanInSemigroup

/-- **Theorem 2.1.** Chandra, Fortune, Lipton, STOC 1983, p.54: "There are constant depth,
polynomial size circuits computing semigroup G iff G is groupfree."

**Formalization Note.** Both directions, for every finite semigroup, every number of bits `k` and
every injective encoding `e`: the page's "an encoding … using k bits is fixed" is any such `e`,
and the statement covers both "some encoding" and "every encoding". -/
theorem theorem_2_1 {S : Type*} [Semigroup S] [Finite S] {k : ℕ} (e : S → Fin k → Bool)
    (he : Function.Injective e) : HasConstDepthPolySize e ↔ IsGroupfree S := by sorry

end FanInSemigroup
