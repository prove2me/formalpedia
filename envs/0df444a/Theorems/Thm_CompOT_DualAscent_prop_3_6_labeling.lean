-- Prove2me | Theorems.Thm_CompOT_DualAscent_prop_3_6_labeling
-- name    : CompOT.DualAscent.prop_3_6_labeling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:16.768515+00:00
-- url     : https://prove2.me/theorems/5a063fcb-5207-4ee1-8e4a-bca3d4d47d6b
-- title:
--   §3.6, proof of Proposition 3.6, pp. 416–417 — without a complementary coupling, some S, S′ closed under balanced edges have 1_Sᵀa > 1_S′ᵀb
-- statement:
--   Let $C \in \mathbb{R}^{n\times m}$, let $a \in \Sigma_n$ and $b \in \Sigma_m$ be histograms (nonnegative entries summing to $1$), and let $(f,g) \in R(C)$ be dual feasible. Suppose that **no** coupling $P \in U(a,b)$ is complementary to $(f,g)$, i.e. there is no $P \in U(a,b)$ supported on the balanced pairs $\{(i,j') : f_i + g_j = C_{i,j}\}$. Then there exist $S \subset [\![n]\!]$ and $S' \subset [\![m]\!]'$ such that
--
--   1. for every $i \in S$, every balanced pair $(i, j')$ has $j' \in S'$, and
--   2. $$\mathbb{1}_S^{\mathsf T}a - \mathbb{1}_{S'}^{\mathsf T}b > 0.$$
--
--   This is the case "throughput strictly smaller than 1" of the proof of Proposition 3.6: the sets $S, S'$ are the labeled nodes of the maximal flow on the bipartite graph of balanced edges, condition 1 makes the direction $(\mathbb 1_S, -\mathbb 1_{S'})$ feasible by Proposition 3.5, and condition 2 makes it an ascent direction.
--
--   **Formalization Note** The book's case hypothesis is that the maximal flow through the network with source capacities $a_i$, sink capacities $b_j$ and uncapacitated balanced edges has throughput strictly smaller than $1$. A flow of throughput $1$ is exactly a coupling $P \in U(a,b)$ supported on balanced edges (the book's extraction $P_{i,j} = f_{ij'}$ and its converse), so the hypothesis is stated flow-free as "no $P \in U(a,b)$ is complementary to $(f,g)$". The page writes $\mathbb 1'_S$ for $\mathbb 1_{S'}$; the Lean states the intended $\sum_{j\in S'} b_j$. $S \neq \emptyset$ is not stated separately; it follows from condition 2 since $b \ge 0$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.6, proof of Proposition 3.6, pp. 416–417 (the case of throughput < 1, ending with "Therefore 1_Sᵀa − 1′_Sᵀb > A − C = 0")

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

namespace CompOT.DualAscent

open Finset

/-- Proof of Proposition 3.6, pp. 416–417 (the case "throughput strictly smaller than 1"):
for histograms `a ∈ Σ_n`, `b ∈ Σ_m` and a dual feasible `(f, g)` to which no coupling
`P ∈ U(a, b)` is complementary, there are index sets `S ⊂ ⟦n⟧`, `S' ⊂ ⟦m⟧'` such that every
pair `(i, j')` balanced for `(f, g)` with `i ∈ S` has `j' ∈ S'`, and
`𝟙_Sᵀ a - 𝟙_{S'}ᵀ b > 0`. -/
theorem prop_3_6_labeling {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : CompOT.Duality.dualFeasible C f g)
    (hno : ¬ ∃ P ∈ CompOT.Assignment.couplings a b, CompOT.Duality.Complementary C P f g) :
    ∃ (S : Finset (Fin n)) (S' : Finset (Fin m)),
      (∀ i ∈ S, ∀ j : Fin m, Balanced C f g i j → j ∈ S') ∧
      0 < ∑ i ∈ S, a i - ∑ j ∈ S', b j := by sorry

end CompOT.DualAscent
