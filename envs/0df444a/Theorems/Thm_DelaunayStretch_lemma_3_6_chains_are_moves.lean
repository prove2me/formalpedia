-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_3_6_chains_are_moves
-- name    : DelaunayStretch.lemma_3_6_chains_are_moves
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:59.761519+00:00
-- url     : https://prove2.me/theorems/0a3afdec-5384-4e23-9514-081c42cfcd5c
-- title:
--   Lemma 3.6 — every disk chain is a sequence of moves
-- statement:
--   Let $(O_1,\dots,O_n;u,v)$ be a disk chain with $n\ge2$, let $\mu_i$ and $\delta_i$ be as in Definition 3.1, and let $s_i=(O_{i+1},G_i,\delta_i)$ for $1\le i\le n-1$. Then:
--
--   1. each $s_i$ is a gate state; $(O_1,O_2)$ is an initial pair leading to $s_1$; for $1\le i\le n-2$, $O_{i+2}$ is a next disk for $s_i$ and the step from $s_i$ to $O_{i+2}$ leads to $s_{i+1}$; and the final step at $s_{n-1}$ ends at $v$;
--   2. for $1\le i\le n$, the move that accounts for $O_i$ has cost $\mu_i-\mu_{i-1}$ and progress $x(c_i)-x(c_{i-1})$.
--
--   Consequently, for every $U\in\mathbb R$,
--
--   $$
--   P(u,v)-U\|u-v\|=\sum_{\text{moves}}\big(\text{cost}-U\cdot\text{progress}\big).
--   $$
--
--   This identifies chains with sequences of moves, so that Theorem 3.9 can sum the inequalities of a feasible potential.
--
--   **Formalization Note** The move accounting for $O_1$ is the initial pair, for $O_i$ ($2\le i\le n-1$) the step from $s_{i-1}$ with new gate $G_i$, and for $O_n$ the final step at $s_{n-1}$; "ends at $v$" is $w_+(O_n)=v$; $c_0=u$, $c_n=v$.
--
--   Differences from the source:
--   - encoding: 'the move that accounts for Oᵢ' and 'the final step ends at v' → the initial pair, step and final-step functions written out for each index, and w₊(Oₙ) = v; reason: the moves are those named in part (1); same content
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: P(u, v), the length of a shortest path from u to v in the ladder graph → the infimum of the weights of walks from u to v in the ladder graph (vertex labels, not points); reason: the ladder graph is finite with nonnegative weights (rails by (C4) and (2.1)), so the infimum is attained and is the shortest-path length
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 3.6, p.18

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsNextDisk

namespace DelaunayStretch

/-- **Lemma 3.6 (Chains are sequences of moves)** (p.18). Let `(O₁, …, Oₙ; u, v)` be a disk
chain with `n ≥ 2`, let `µᵢ` and `δᵢ` be as in Definition 3.1, and let
`sᵢ = (Oᵢ₊₁, Gᵢ, δᵢ)` for `1 ≤ i ≤ n − 1`. Then:

1. each `sᵢ` is a gate state; `(O₁, O₂)` is an initial pair leading to `s₁`; for
   `1 ≤ i ≤ n − 2`, `Oᵢ₊₂` is a next disk for `sᵢ`, and the step from `sᵢ` to `Oᵢ₊₂` leads to
   `sᵢ₊₁`; and the final step at `sₙ₋₁` ends at `v`;
2. for `1 ≤ i ≤ n`, the move that accounts for `Oᵢ` has cost `µᵢ − µᵢ₋₁` and progress
   `x(cᵢ) − x(cᵢ₋₁)`.

Consequently, for every `U ∈ ℝ`, `P(u, v) − U‖u − v‖` is the sum of cost `− U ·` progress over
these `n` moves.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 3.6, p.18.

**Formalization Note** The move accounting for `O₁` is that of the initial pair `(O₁, O₂)`, the
one for `Oᵢ` (`2 ≤ i ≤ n − 1`) is the step from `sᵢ₋₁` to `Oᵢ₊₁` (new gate `Gᵢ`), and the one
for `Oₙ` is the final step at `sₙ₋₁`; the final step ends at `w₊(Oₙ)`. `c₀ = u`, `cₙ = v`. -/
theorem lemma_3_6_chains_are_moves (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    let s : ℕ → GateState := fun i => ⟨C.O (i + 1), C.a i, C.b i, C.delta i⟩
    ((∀ i, 1 ≤ i → i + 1 ≤ C.n → (s i).IsGateState) ∧
      IsInitialPair (C.O 1) (C.O 2) (C.a 1) (C.b 1) ∧
      initialState (C.O 1) (C.O 2) (C.a 1) (C.b 1) = s 1 ∧
      (∀ i, 1 ≤ i → i + 2 ≤ C.n →
        IsNextDisk (s i) (C.O (i + 2)) (C.a (i + 1)) (C.b (i + 1)) ∧
          stepState (s i) (C.O (i + 2)) (C.a (i + 1)) (C.b (i + 1)) = s (i + 1)) ∧
      (s (C.n - 1)).O.wPlus = C.v) ∧
    (initialCost (C.O 1) (C.a 1) (C.b 1) = C.mu 1 - C.mu 0 ∧
      initialProgress (C.O 1) (C.a 1) (C.b 1) = (C.c 1).re - (C.c 0).re ∧
      (∀ i, 2 ≤ i → i + 1 ≤ C.n →
        stepCost (s (i - 1)) (C.a i) (C.b i) = C.mu i - C.mu (i - 1) ∧
          stepProgress (s (i - 1)) (C.a i) (C.b i) = (C.c i).re - (C.c (i - 1)).re) ∧
      finalCost (s (C.n - 1)) = C.mu C.n - C.mu (C.n - 1) ∧
      finalProgress (s (C.n - 1)) = (C.c C.n).re - (C.c (C.n - 1)).re) ∧
    (∀ U : ℝ, C.shortestPath - U * dist C.u C.v =
      (initialCost (C.O 1) (C.a 1) (C.b 1) - U * initialProgress (C.O 1) (C.a 1) (C.b 1)) +
        (∑ i ∈ Finset.Ico 1 (C.n - 1),
          (stepCost (s i) (C.a (i + 1)) (C.b (i + 1)) -
            U * stepProgress (s i) (C.a (i + 1)) (C.b (i + 1)))) +
        (finalCost (s (C.n - 1)) - U * finalProgress (s (C.n - 1)))) := by sorry

end DelaunayStretch
