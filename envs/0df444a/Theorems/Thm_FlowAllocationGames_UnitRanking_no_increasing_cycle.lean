-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_no_increasing_cycle
-- name    : FlowAllocationGames.UnitRanking.no_increasing_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:50.441591+00:00
-- url     : https://prove2.me/theorems/c06c02da-3764-4bbb-a1bb-6b86707a3955
-- title:
--   Proof of Theorem 9, p. 24 — no closed chain of increases beyond an optimal circulation
-- statement:
--   Let $f^*$ be an optimal circulation of $G'$ and $f'$ an integral flow on $G$ with $f'_e \le c_e$ for every edge. It is impossible that
--
--   1. some edge has $f'_e > f^*_e$, and
--   2. every edge $e$ with $f'_e > f^*_e$ has an incoming edge $e'$ at its tail with $f'_{e'} > f^*_{e'}$.
--
--   Under conditions 1 and 2 one could follow increased edges backwards indefinitely, find a cycle of edges that all carry more flow in $f'$ than in $f^*$, and push one more unit around it, contradicting the optimality of $f^*$.
--
--   Differences from the source:
--   - reading: "We can repeat this argument indefinitely. As such, there must be a cycle …" → the negation of: some edge is increased and every increased edge has an increased edge into its tail; reason: this is the closed form of "repeat indefinitely"; the cycle and the contradiction are the content to prove
--   - generalization: f̂′, the clearing state of the deviation → any integral flow f′ within the capacities; reason: clearing states respect the capacities, so the page's case is an instance
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 24, ¶2

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMaxCirculation

namespace FlowAllocationGames.UnitRanking

/-- **No flow can exceed an optimal circulation along a closed chain.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 24: "We can repeat this argument indefinitely. As such, there must be a cycle of edges that all
have more flow in f̂′ than in f∗. Such a cycle can be used to increase the circulation, which
contradicts that f∗ is an optimal circulation in G′."

Let `x` be an optimal circulation in `G′` and `f'` a flow on `G` within the capacities. It is
impossible that some edge has strictly more flow in `f'` than in `x` and that every such edge has
an incoming edge at its tail that also has strictly more flow in `f'` than in `x`.

**Formalization Note.** The second condition is "we can repeat this argument indefinitely"; the
existence of a cycle of such edges, and its use to increase the circulation, are what the page
claims and what the proof has to supply. -/
theorem no_increasing_cycle {n m : ℕ} (Γ : Game n m) (x : Circ n m) (hx : IsMaxCirculation Γ x)
    (f' : Fin m → ℕ) (hf' : ∀ e, f' e ≤ Γ.c e) :
    ¬ ((∃ e, x.flow e < f' e) ∧
      ∀ e, x.flow e < f' e → ∃ e', Γ.head e' = Γ.tail e ∧ x.flow e' < f' e') := by sorry

end FlowAllocationGames.UnitRanking
