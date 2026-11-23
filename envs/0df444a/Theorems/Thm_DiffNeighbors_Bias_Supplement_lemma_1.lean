-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_Supplement_lemma_1
-- name    : DiffNeighbors.Bias.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:14:34.399071+00:00
-- url     : https://prove2.me/theorems/a86007b6-ca1a-4fa1-85ae-801b2a9f1767
-- title:
--   Lemma 1 — the absolute block mixed difference is bounded by mnLδ²
-- statement:
--   Let $I$ be a finite unit set, $G$ an undirected graph without self-loops, and $f_i:\{0,1\}^I\to\mathbb R$ the potential outcomes. Write $f_i^a(z)=f_i(z^{z_i=a})$ and let $\mathcal N_i$ denote its neighbours. Suppose $\delta>0$ and $f_i^a(z)=g_i^a(\delta z)$, with $g_i^a$ twice differentiable within $[0,\delta]^I$ and all mixed second derivatives for distinct neighbours bounded in absolute value by $L$ (Assumption 2).
--
--   For any unit $i$, binary treatment $a$, treatment vector $z$, and disjoint subsets $S,T\subseteq\mathcal N_i$ of sizes $m,n$, let $D_{S,T}$ change whole blocks to zero or one, retaining every other entry. Then
--   $$|D_{S,T}f_i^a(z)|\le mnL\delta^2.$$
--   Taking $S=C_j\cap\mathcal N_i$, $T=C_k\cap\mathcal N_i$ recovers all cluster sizes in the printed lemma. The absolute bound includes its one-sided conclusion and the mirror used by Theorem 3. Neighborhood interference is unnecessary.
--
--   Differences from the source:
--   - generalization: two distinct neighbour clusters other than the own cluster, of sizes m,n, and a one-sided block inequality → any disjoint S,T contained in N_i, including empty blocks, and an absolute bound |S||T|Lδ²; reason: the source clusters give S=C_j∩N_i and T=C_k∩N_i; the same signed bound applied to -g gives the other sign, as used on p. 29
--   - reading: scaled functions and second derivatives on the box in §2.2 and Assumption 2 → functions on all unit coordinates, parameterized at δz, twice differentiable within [0,δ]^I with bounded mixed within-derivatives only for distinct neighbours; reason: neighbour functions compose with the projection; p. 6 specifies the box and presupposes these derivatives exist, with no global regularity requirement
--   - generalization: Assumption 1 holds throughout the paper → neighborhood interference is omitted for this local finite-difference bound; reason: only the parameterization and mixed derivative bounds are used; every neighborhood-interference model remains an instance
--   - encoding: binary treatment vectors on [N] → Bool-valued vectors on finite types, with the published conditional outcome and signed finite difference; reason: Bool encodes zero and one and all finite source instances are retained
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 28, Appendix A.2, Lemma 1; p. 29, use of the absolute bound

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Supplement_SmoothModel
import Definitions.Def_DiffNeighbors_Bias_Supplement_BlockModel

namespace DiffNeighbors.Bias.Supplement

/-- Lemma 1, Appendix A.2, p. 28, in its two-sided form used on p. 29.
Any two disjoint subsets of N_i are allowed; the source clusters are the
special case S = C_j ∩ N_i, T = C_k ∩ N_i. Empty blocks are permitted.
Neighborhood interference is unnecessary for this assertion. -/
theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (f : ι → (ι → Bool) → ℝ)
    (g : ι → Bool → (ι → ℝ) → ℝ) (δ L : ℝ) (hδ : 0 < δ)
    (hg : SmoothInterference G f g δ L)
    (i : ι) (a : Bool) (z : ι → Bool) (S T : Finset ι)
    (hS : S ⊆ G.neighborFinset i) (hT : T ⊆ G.neighborFinset i)
    (hST : Disjoint S T) :
    |blockDiff (condOutcome f i a) S T z| ≤
      (S.card : ℝ) * (T.card : ℝ) * L * δ ^ 2 := by sorry

end DiffNeighbors.Bias.Supplement
