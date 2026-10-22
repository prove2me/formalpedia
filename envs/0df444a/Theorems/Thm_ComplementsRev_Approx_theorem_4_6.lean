-- Prove2me | Theorems.Thm_ComplementsRev_Approx_theorem_4_6
-- name    : ComplementsRev.Approx.theorem_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:03.8294+00:00
-- url     : https://prove2.me/theorems/6dcf9d8f-f38e-4c52-a0da-a04ee87909ac
-- title:
--   Theorem 4.6 — Partition-Edges bound
-- statement:
--   Let $E$ be a finite family of nonempty hyperedges on the item set $M$. Run the paper's Partition-Edges procedure with any ordering of the current edges at each round. Its output $H_1,\ldots,H_k$ partitions $E$, and each $T\in H_x$ contains an item absent from every other edge of $H_x$. Moreover,
--
--   $$k\le\max_{i\in M}|\{T\in E:i\in T\}|.$$
--
--   This partition controls how many groups of simultaneously priced hyperedges are needed in the SINGLE estimate.
--
--   **Formalization Note** The input excludes the empty edge, for which Figure 1 does not terminate. The statement applies to the algorithm's actual output, with a list specifying the processing order in each round; it includes coverage and disjointness of the output blocks.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Figure 1 and Theorem 4.6, pp. 9–10

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Theorem 4.6, pp. 9–10: Figure 1 returns the stated partition. -/
theorem theorem_4_6 (E : Finset (Finset ι)) (hE : (∅ : Finset ι) ∉ E)
    (σ : ℕ → Finset (Finset ι) → List (Finset ι))
    (hσ : ∀ round F, (σ round F).toFinset = F)
    (hσ_nodup : ∀ round F, (σ round F).Nodup) :
    let L := partitionEdges σ 0 E.card E
    L.Pairwise (fun H K => Disjoint H K) ∧
    L.foldl (· ∪ ·) ∅ = E ∧
    (∀ H ∈ L, ∀ T ∈ H, ¬ T ⊆ (H.erase T).biUnion id) ∧
    L.length ≤ Finset.univ.sup (fun i : ι => (E.filter (fun T => i ∈ T)).card) := by sorry

end ComplementsRev.Approx
