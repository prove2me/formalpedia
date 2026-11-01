-- Prove2me | Theorems.Thm_FairFlows_lemma_5_2
-- name    : FairFlows.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:21.415218+00:00
-- url     : https://prove2.me/theorems/ad21d288-108c-4c9b-bdde-20f5b303a08f
-- title:
--   Lemma 5.2 — pre-dec-min flows are $Q⃛'$, and $F$-dec-min flows are the $F$-dec-min elements of $Q⃛'$
-- statement:
--   Assume (5.1), let $\mathcal C'$ be a dual optimal chain, let $(f',g')$ be defined from $\mathcal C'$ by (5.2)–(5.3), and let Q⃛$'$ $:=$ Q⃛$(f',g';m)$ (5.4). Then:
--
--   1. (A) an $m$-flow $z\in$ Q⃛ is pre-dec-min on $F$ if and only if $z\in$ Q⃛$'$;
--   2. (B) an $m$-flow $z\in$ Q⃛ is $F$-dec-min (in Q⃛) if and only if $z$ is an $F$-dec-min element of Q⃛$'$.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: decreasingly minimal on F → no member of the set has a non-increasingly sorted value list on F that is lexicographically smaller (List.Lex (· < ·)); reason: Lean convention; this is the paper's definition
--   - generalization: §5 assumes the underlying undirected graph of D is connected (p.13) → no connectivity assumption; reason: nothing in §§4–5 uses it and Theorem 2.1 does not assume it; connected digraphs are the special case
--   - reading: "the chain C′ of Theorem 5.1" (a dual optimal chain) → every dual optimal chain C′; reason: the proof uses only the properties of Theorem 5.1, so the statement holds for each such chain; this is the stronger reading
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Lemma 5.2, p.14 ((5.2)–(5.4) p.14)

import Mathlib
import Definitions.Def_FairFlows_DecMin
import Definitions.Def_FairFlows_Section5

set_option autoImplicit false

namespace FairFlows

/-- Lemma 5.2 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.14). Given (5.1), let `C′` be a dual optimal chain and let
`(f′, g′)` be defined from `C′` by (5.2)–(5.3), `Q⃛′ := Q⃛(f′, g′; m)` (5.4). (A) An `m`-flow
`z ∈ Q⃛` is pre-dec-min on `F` if and only if `z ∈ Q⃛′`. (B) An `m`-flow `z ∈ Q⃛` is `F`-dec-min if
and only if `z` is an `F`-dec-min element of `Q⃛′`.

**Formalization Note** "The chain `C′` of Theorem 5.1" is read as an arbitrary dual optimal
chain; the lemma is stated for every one of them. -/
theorem lemma_5_2 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hS : Setting51 D f g m F) (C : Finset (Finset V)) (hC : IsDualOptimalChain D f g m F C) :
    (∀ z ∈ intFlows D f g m,
      (IsPreDecMin D f g m F z ↔ z ∈ intFlows D (fPrime D f g F C) (gPrime D f g F C) m)) ∧
    (∀ z ∈ intFlows D f g m,
      (IsDecMinOn (intFlows D f g m) F z ↔
        IsDecMinOn (intFlows D (fPrime D f g F C) (gPrime D f g F C) m) F z)) := by sorry

end FairFlows
