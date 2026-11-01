-- Prove2me | Theorems.Thm_FairFlows_tight_edge_reduction
-- name    : FairFlows.tight_edge_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:25.768981+00:00
-- url     : https://prove2.me/theorems/7c56adb6-604b-40a0-81f9-8c43fb3b87b3
-- title:
--   §2.2 — removing a tight edge from $F$ does not change $F$-dec-min flows
-- statement:
--   Let $e\in F$ be an $(f,g)$-tight edge, $f(e)=g(e)$. Then an integral $(f,g)$-bounded $m$-flow $z$ is decreasingly minimal on $F$ if and only if $z$ is decreasingly minimal on $F-e$ (both among the members of Q⃛$(f,g;m)$).
--
--   This is the reduction that lets the proof of Theorem 2.1 assume that $F$ contains no tight edges.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: decreasingly minimal on F → no member of the set has a non-increasingly sorted value list on F that is lexicographically smaller (List.Lex (· < ·)); reason: Lean convention; this is the paper's definition
--   - generalization: stated in the setting of Theorem 2.1 (f ≤ g, m̃(V) = 0, f and g finite on F) → no assumption besides e ∈ F tight; reason: a tight edge has equal finite bounds, so all members of Q⃛ agree on it; the setting of Theorem 2.1 is a special case
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §2.2, p.7

import Mathlib
import Definitions.Def_FairFlows_Network
import Definitions.Def_FairFlows_DecMin

set_option autoImplicit false

namespace FairFlows

/-- The tight-edge reduction of §2.2 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.7): if `e ∈ F` is `(f, g)`-tight, then an
integral `(f, g)`-bounded `m`-flow `z` is `F`-dec-min if and only if `z` is `(F − e)`-dec-min.

**Formalization Note** No standing assumption of §2 (`f ≤ g`, `m̃(V) = 0`, finiteness on `F`) is
needed or assumed; a tight edge has finite equal bounds, so every member of `Q⃛` takes the same
value on it. -/
theorem tight_edge_reduction {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (e : A) (he : e ∈ F) (ht : IsTight f g e) (z : A → ℤ) :
    IsDecMinOn (intFlows D f g m) F z ↔ IsDecMinOn (intFlows D f g m) (F.erase e) z := by sorry

end FairFlows
