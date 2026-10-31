-- Prove2me | Theorems.Thm_CutSetEnum_claim_3_1
-- name    : CutSetEnum.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:24.269709+00:00
-- url     : https://prove2.me/theorems/58157eb7-7dda-463a-ad77-adbb038ec98d
-- title:
--   Claim 3.1 — the source minimal minimum $(S,T)$-terminal cut has cut-set $\delta(U)$
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $k\ge2$, and $(U,\bar U)$ a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Let $S\subseteq U$ and $T\subseteq\bar U$ be non-empty sets with $|S|\le 2k-1$ and $|T|\le 2k-1$ such that
--
--   1. every minimum $(S,\bar U)$-terminal cut $(A,\bar A)$ has $\delta(A)=\delta(U)$ (as given by Theorem 2.1), and
--   2. every minimum $(U,T)$-terminal cut $(A,\bar A)$ has $\delta(A)=\delta(U)$ (as given by Corollary 3.1).
--
--   **Claim 3.1.** If $(Y,\bar Y)$ is the source minimal minimum $(S,T)$-terminal cut, then
--   $$
--   \delta(Y)=\delta(U).
--   $$
--
--   Applied to both sides of $(U,\bar U)$, this is the step of the proof of Theorem 1.4 that shows every hyperedge of $\delta(U)$ crosses every minimum $(S,T)$-terminal cut.
--
--   Differences from the source:
--   - encoding: S, T as produced by Theorem 2.1 and Corollary 3.1 → hypotheses S ⊆ U, S non-empty, |S| ≤ 2k − 1, the recovery property of S, and the same for T; reason: exactly the properties the proof takes from Theorem 2.1 and Corollary 3.1; non-emptiness because terminal cuts are defined only for non-empty terminal sets
--   - encoding: (Y, Ȳ) the source minimal minimum (S, T)-terminal cut → IsSourceMinMinTerminalCut H S T Y (minimum and contained in every minimum cut); reason: the minimum cuts have a least source set (published source_max_cut), so inclusion-minimal and least coincide
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
--   - encoding: δ(A) = δ(U), equality of sets of hyperedges → cutSet H A = cutSet H U, equality of sub-multisets of the hyperedge multiset; reason: parallel copies of a hyperedge cross a cut together, so multiset and set equality agree
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 1.4, proof, Claim 3.1, p.15 (PDF 16)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Claim 3.1: the source minimal minimum `(S, T)`-terminal cut has cut-set `δ(U)`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 1.4, proof, Claim 3.1, p.15
(PDF 16), with the set-up of that proof: "By Theorem 2.1, there exists a subset S ⊆ U with
|S| ≤ 2k − 1 such that every minimum (S, Ū)-terminal cut (A, Ā) has δ(A) = δ(U). By
Corollary 3.1, there exists a subset T ⊆ Ū with |T| ≤ 2k − 1 such that every minimum
(U, T)-terminal cut (A, Ā) has δ(A) = δ(U). … Claim 3.1. Let (Y, Ȳ) be the source minimal
minimum (S, T)-terminal cut. Then δ(Y) = δ(U)."

**Formalization Note.** The hypotheses are those of Theorem 1.4 (`k ≥ 2`; `U`, `Uᶜ` non-empty;
`IsOptKCutValue H k (d H U)`) together with the properties of `S` and `T` that the proof takes from
Theorem 2.1 and Corollary 3.1. `S` and `T` are assumed non-empty, as the paper's definition of
terminal cuts requires. `Y` is the source minimal minimum `(S, T)`-terminal cut
(`IsSourceMinMinTerminalCut`). -/
theorem claim_3_1
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S T : Finset V)
    (hSU : S ⊆ U) (hSne : S.Nonempty) (hScard : S.card ≤ 2 * k - 1)
    (hSrec : ∀ A : Finset V, IsMinTerminalCut H S Uᶜ A → cutSet H A = cutSet H U)
    (hTU : T ⊆ Uᶜ) (hTne : T.Nonempty) (hTcard : T.card ≤ 2 * k - 1)
    (hTrec : ∀ A : Finset V, IsMinTerminalCut H U T A → cutSet H A = cutSet H U)
    (Y : Finset V) (hY : IsSourceMinMinTerminalCut H S T Y) :
    cutSet H Y = cutSet H U := by sorry

end CutSetEnum
