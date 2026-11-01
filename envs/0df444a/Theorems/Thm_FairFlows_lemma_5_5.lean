-- Prove2me | Theorems.Thm_FairFlows_lemma_5_5
-- name    : FairFlows.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:29.163995+00:00
-- url     : https://prove2.me/theorems/400070eb-3dd0-49d4-b4e3-84ccb7e322d8
-- title:
--   Lemma 5.5 — the members of $Q⃛'$ are value-equivalent on $L'$
-- statement:
--   Assume (5.1), let $\mathcal C'$ be a dual optimal chain, $(f',g')$ the bounds (5.2)–(5.3), Q⃛$'$ $=$ Q⃛$(f',g';m)$, and $L'$ the edges of $L$ entering a member of $\mathcal C'$. Then any two members of Q⃛$'$ are value-equivalent on $L'$: their restrictions to $L'$, both arranged in decreasing order, are equal.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - generalization: §5 assumes the underlying undirected graph of D is connected (p.13) → no connectivity assumption; reason: nothing in §§4–5 uses it and Theorem 2.1 does not assume it; connected digraphs are the special case
--   - reading: "the chain C′ of Theorem 5.1" (a dual optimal chain) → every dual optimal chain C′; reason: the proof uses only the properties of Theorem 5.1, so the statement holds for each such chain; this is the stronger reading
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Lemma 5.5, p.15

import Mathlib
import Definitions.Def_FairFlows_DecMin
import Definitions.Def_FairFlows_Section5

set_option autoImplicit false

namespace FairFlows

/-- Lemma 5.5 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.15). Given (5.1), a dual optimal chain `C′`, `(f′, g′)` from
(5.2)–(5.3) and `Q⃛′ = Q⃛(f′, g′; m)`, the members of `Q⃛′` are value-equivalent on `L′`: their
restrictions to `L′`, both arranged in decreasing order, are equal.

**Formalization Note** Stated for every dual optimal chain. -/
theorem lemma_5_5 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hS : Setting51 D f g m F) (C : Finset (Finset V)) (hC : IsDualOptimalChain D f g m F C) :
    ∀ z ∈ intFlows D (fPrime D f g F C) (gPrime D f g F C) m,
      ∀ z' ∈ intFlows D (fPrime D f g F C) (gPrime D f g F C) m,
        decSorted (Lprime D g F C) z = decSorted (Lprime D g F C) z' := by sorry

end FairFlows
