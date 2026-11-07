-- Prove2me | Theorems.Thm_ClawFreeChoosable_theorem_1_3_precolouring_extension
-- name    : ClawFreeChoosable.theorem_1_3_precolouring_extension
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:10.269464+00:00
-- url     : https://prove2.me/theorems/38fd6c00-26bd-4b0c-a33f-7aab9ba44985
-- title:
--   Theorem 1.3 — precolouring extension for claw-free perfect graphs
-- statement:
--   Let $G$ be a finite claw-free perfect graph, let $k \ge \omega(G)$ be an integer, and let $S \subseteq V(G)$ be a clique of simplicial vertices, possibly empty. If $\phi$ is a proper colouring of $G[S]$ and $L$ is a list assignment with $|L(v)| \ge k$ for $v \in V(G) \setminus S$, then there is a proper colouring $f$ of $G$ with
--   $$f|_S = \phi \quad\text{and}\quad f(v) \in L(v) \text{ for all } v \notin S.$$
--
--   This is the paper's stronger form of a conjecture of Chudnovsky and Seymour (without its connectivity assumption); Theorem 1.1 is its case $S = \emptyset$, $k = \omega(G)$.
--
--   Differences from the source:
--   - encoding: ϕ a colouring of G[S], lists L(v) for v ∈ V(G) \ S, colours unspecified → ϕ : V → α and L : V → Finset α over an arbitrary colour type α, only ϕ on S and L off S read; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Theorem 1.3, p.2 (PDF p.5)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_ClawFreeChoosable_IsClawFree
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Theorem 1.3 (Precolouring extension)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.2). Let `G` be a claw-free perfect graph,
let `k ≥ ω(G)` be an integer, and let `S ⊆ V(G)` be a clique of simplicial vertices, possibly
empty. If `ϕ` is a proper colouring of `G[S]` and `|L(v)| ≥ k` for `v ∈ V(G) \ S`, then there is a
proper colouring `f` of `G` with `f|S = ϕ` and `f(v) ∈ L(v)` for `v ∉ S`.

**Formalization Note.** Colours range over an arbitrary type `α`; `ϕ` and `L` are total maps on
`V`, of which only `ϕ` on `S` and `L` off `S` are read. -/
theorem theorem_1_3_precolouring_extension {V : Type} [Fintype V] (G : SimpleGraph V)
    (hclaw : IsClawFree G) (hperf : StrongPerfectGraph.Main.IsPerfect G) (k : ℕ)
    (hk : G.cliqueNum ≤ k) (α : Type) (S : Set V) (hS : IsSimplicialClique G S) (ϕ : V → α)
    (hϕ : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ϕ u ≠ ϕ v) (L : V → Finset α)
    (hL : ∀ v, v ∉ S → k ≤ (L v).card) :
    ∃ f : V → α, (∀ u v, G.Adj u v → f u ≠ f v) ∧ (∀ s ∈ S, f s = ϕ s) ∧
      ∀ v, v ∉ S → f v ∈ L v := by sorry

end ClawFreeChoosable
