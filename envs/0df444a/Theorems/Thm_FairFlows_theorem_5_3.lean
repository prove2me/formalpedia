-- Prove2me | Theorems.Thm_FairFlows_theorem_5_3
-- name    : FairFlows.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:37.241523+00:00
-- url     : https://prove2.me/theorems/031c843d-49a3-499d-9fcc-c45580f057b8
-- title:
--   Theorem 5.3 — one tightening step: $F$-dec-min in Q⃛ iff $F'$-dec-min in $Q⃛'$, narrow on $F-F'$
-- statement:
--   Assume (5.1). There is a pair $(f',g')$ of integer-valued functions on $A$ ($f':A\to\mathbb Z\cup\{-\infty\}$, $g':A\to\mathbb Z\cup\{+\infty\}$) with $f\le f'\le g'\le g$ and a proper subset $F'\subset F$ such that an element $z$ of Q⃛ is an $F$-dec-min member of Q⃛ if and only if $z$ is an $F'$-dec-min member of Q⃛$'$ $=$ Q⃛$(f',g';m)$. In addition, the box $T(f',g')$ is narrow on $F-F'$:
--   $$0\le g'(e)-f'(e)\le 1\qquad\text{for every } e\in F-F'.$$
--
--   Theorem 2.1 follows by induction on $|F|$ from this step and the two reductions of §2.2.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: decreasingly minimal on F → no member of the set has a non-increasingly sorted value list on F that is lexicographically smaller (List.Lex (· < ·)); reason: Lean convention; this is the paper's definition
--   - generalization: §5 assumes the underlying undirected graph of D is connected (p.13) → no connectivity assumption; reason: nothing in §§4–5 uses it and Theorem 2.1 does not assume it; connected digraphs are the special case
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 5.3, p.14

import Mathlib
import Definitions.Def_FairFlows_DecMin
import Definitions.Def_FairFlows_Section5

set_option autoImplicit false

namespace FairFlows

/-- Theorem 5.3 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.14). Given (5.1), there is a pair `(f′, g′)` of integer-valued
functions on `A` with `f ≤ f′ ≤ g′ ≤ g` and a set `F′ ⊂ F` such that an element `z` of `Q⃛` is an
`F`-dec-min member of `Q⃛` if and only if `z` is an `F′`-dec-min member of
`Q⃛′ = Q⃛(f′, g′; m)`. In addition, the box `T(f′, g′)` is narrow on `F − F′`:
`0 ≤ g′(e) − f′(e) ≤ 1` for every `e ∈ F − F′`.

**Formalization Note** `f′ : A → ℤ ∪ {−∞}` and `g′ : A → ℤ ∪ {+∞}`; `F′ ⊂ F` is a proper
subset; narrowness includes finiteness of `f′(e)`, `g′(e)`. -/
theorem theorem_5_3 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hS : Setting51 D f g m F) :
    ∃ (f' : A → WithBot ℤ) (g' : A → WithTop ℤ) (F' : Finset A),
      f ≤ f' ∧ BoundsLE f' g' ∧ g' ≤ g ∧ F' ⊂ F ∧
      (∀ z ∈ intFlows D f g m,
        (IsDecMinOn (intFlows D f g m) F z ↔ IsDecMinOn (intFlows D f' g' m) F' z)) ∧
      ∀ e ∈ F \ F', NarrowAt f' g' e := by sorry

end FairFlows
