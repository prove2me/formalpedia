-- Prove2me | Theorems.Thm_FairFlows_claim_5_4
-- name    : FairFlows.claim_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:38.222092+00:00
-- url     : https://prove2.me/theorems/3607dc71-5b1b-4250-9cac-4253212628f8
-- title:
--   Claim 5.4 — some edge of $L$ enters a member of the dual optimal chain
-- statement:
--   Assume (5.1) and let $\mathcal C'$ be a dual optimal chain. Then the set $L'$ of those elements of $L=\{e\in F: g(e)=\beta\}$ that enter at least one member of $\mathcal C'$ is non-empty.
--
--   Consequently $F':=F-L'$ is a proper subset of $F$, which drives the induction on $|F|$.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - generalization: §5 assumes the underlying undirected graph of D is connected (p.13) → no connectivity assumption; reason: nothing in §§4–5 uses it and Theorem 2.1 does not assume it; connected digraphs are the special case
--   - reading: "the chain C′ of Theorem 5.1" (a dual optimal chain) → every dual optimal chain C′; reason: the proof uses only the properties of Theorem 5.1, so the statement holds for each such chain; this is the stronger reading
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Claim 5.4, p.14 (in the proof of Theorem 5.3)

import Mathlib
import Definitions.Def_FairFlows_Section5

set_option autoImplicit false

namespace FairFlows

/-- Claim 5.4 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.14, in the proof of Theorem 5.3). Given (5.1) and a dual optimal
chain `C′`, the set `L′` of those elements of `L` that enter at least one member of `C′` is
non-empty.

**Formalization Note** Stated for every dual optimal chain. -/
theorem claim_5_4 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (hS : Setting51 D f g m F) (C : Finset (Finset V)) (hC : IsDualOptimalChain D f g m F C) :
    (Lprime D g F C).Nonempty := by sorry

end FairFlows
