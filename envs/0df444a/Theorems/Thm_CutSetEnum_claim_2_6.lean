-- Prove2me | Theorems.Thm_CutSetEnum_claim_2_6
-- name    : CutSetEnum.claim_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:06.728378+00:00
-- url     : https://prove2.me/theorems/aa17fff1-3f1f-42f0-9b86-6af02ce6acde
-- title:
--   Claim 2.6 — a hyperedge meeting $W$ and $Z$ inside $W\cup Z$
-- statement:
--   **Setting (proof of Lemma 2.1, p.11).** Let $G=(V,E)$ be a hypergraph, $k\ge2$, and $(U,\bar U)$ a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Let $\mathcal C=\{Q\subseteq V:\ \bar U\subsetneq Q,\ d(Q)\le d(U),\ \delta(Q)\ne\delta(U)\}$ and let $S\subseteq U$ be an inclusion-wise minimal transversal of $\mathcal C$. Suppose, for contradiction, that $S=\{u_1,\dots,u_p\}$ with $p\ge 2k$ distinct vertices. For every non-empty $X\subseteq U$ let $(H_X,\bar H_X)$ be the source minimal minimum $(X,\bar U)$-terminal cut. Write $S-u_i=S\setminus\{u_i\}$ and $S-u_i-u_j=S\setminus\{u_i,u_j\}$.
--
--   For $i\in[p-1]$ (every index except the last) let $(\bar A_i,A_i)=(H_{S-u_i},\bar H_{S-u_i})$, and put
--   $$
--   W=\bigcup_{1\le i<j\le p-1}(A_i\cap A_j),\qquad Z=\bigcap_{i\in[p-1]}\bar A_i .
--   $$
--
--   **Claim 2.6.** There exists a hyperedge $e\in E$ such that
--   $$
--   e\cap W\ne\emptyset,\qquad e\cap Z\ne\emptyset,\qquad e\subseteq W\cup Z.
--   $$
--
--   This is the hyperedge that makes the strict conclusion of Theorem 1.5 apply, with $R=\{u_p\}$ and $S'=S-u_p$.
--
--   Lemma 2.1 shows that this setting cannot occur; the claim is one step of that proof by contradiction and is posed, as in the paper, inside the setting.
--
--   **Formalization Note** The setting is carried as hypotheses: $S$ is the image of an injective map $u:\{0,\dots,p-1\}\to V$ (0-based indices), $H_X$ is a function `Hs` with `IsSourceMinMinTerminalCut H X Uᶜ (Hs X)` for every non-empty $X\subseteq U$, and $S-u_i$ is `S.erase (u i)`.
--   The paper's $[p-1]$ is the set of 0-based indices $i$ with $i<p-1$.
--
--   Differences from the source:
--   - encoding: S = {u₁, …, u_p}, p ≥ 2k, indices 1…p → S = image of an injective u : Fin p → V, 2k ≤ p, indices 0…p−1; reason: relabelling of the same p distinct vertices
--   - encoding: (H_X, H̅_X) the source minimal minimum (X, Ū)-terminal cut, for X ⊆ U → a function Hs with IsSourceMinMinTerminalCut H X Uᶜ (Hs X) for every non-empty X ⊆ U; reason: the cut exists and is unique for non-empty X (published source_max_cut); the paper only uses non-empty X
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: the (X, Ū)-terminal cuts behind H_X, 2-partitions with X ⊆ A ⊆ V \ Ū → published IsTerminalCut X Uᶜ A := X ⊆ A ∧ Disjoint A Uᶜ (no separate 2-partition clause), inside IsSourceMinMinTerminalCut; reason: X is non-empty and Ū is non-empty, so the two coincide
--   - encoding: [p − 1] = {1, …, p − 1}; W, Z defined in the text → indices i : Fin p with i.val < p − 1; W, Z binders pinned by equations hW, hZ; reason: 0-based relabelling of the same index set (all but u_p); same sets
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Lemma 2.1, proof, Claim 2.6, p.14 (PDF 15)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Claim 2.6: a hyperedge meeting `W` and `Z` inside `W ∪ Z`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Lemma 2.1, proof, Claim 2.6, p.14 (PDF 15),
with its set-up on the same page: "Let R := {u_p}, S′ := S − u_p, and (Āᵢ, Aᵢ) :=
(H_{S−u_i}, H̅_{S−u_i}) for every i ∈ [p − 1]. … Let W := ∪_{1≤i<j≤p−1}(Aᵢ ∩ Aⱼ) and
Z := ∩_{i∈[p−1]} Āᵢ as in the statement of Theorem 1.5. Claim 2.6. There exists a hyperedge
e ∈ E such that e ∩ W ≠ ∅, e ∩ Z ≠ ∅, and e ⊆ W ∪ Z."

Here `Aᵢ = (Hs (S.erase (u i)))ᶜ` and `Āᵢ = Hs (S.erase (u i))` for the indices `i` other than
the last one, `W` is the union over pairs `i < j` of such indices of `Aᵢ ∩ Aⱼ`, and `Z` is the
intersection over such indices of `Āᵢ`. `W` and `Z` are binders pinned by their defining
equations `hW`, `hZ`.

**Formalization Note (the Lemma 2.1 setting).** This claim lives inside the proof of Lemma 2.1,
whose standing hypotheses are carried as binders: `k ≥ 2`; `(U, Uᶜ)` a 2-partition with
`d(U) = OPT_k-cut` (`IsOptKCutValue`); `S` a minimal transversal of the collection `C` inside `U`
(`IsMinTransversal`); the proof's contradiction hypothesis `|S| = p ≥ 2k`, with
`S = {u 0, …, u (p-1)}` for an injective `u : Fin p → V` (0-based indices); and `Hs X`, the
paper's `H_X`, the source minimal minimum `(X, Uᶜ)`-terminal cut for every non-empty `X ⊆ U`.
`S − uᵢ` is `S.erase (u i)` and `S − uᵢ − uⱼ` is `(S.erase (u i)).erase (u j)`. Lemma 2.1 shows
that this setting never occurs; the claim is posed, as in the paper, inside it. The paper's `[p − 1]` (all indices but the removed `u_p`) is the set of `i : Fin p` with
`i.val < p - 1`. -/
theorem claim_2_6
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (W Z : Finset V)
    (hW : W = (Finset.univ.filter (fun ij : Fin p × Fin p =>
        ij.1 < ij.2 ∧ ij.2.val < p - 1)).biUnion
        (fun ij => (Hs (S.erase (u ij.1)))ᶜ ∩ (Hs (S.erase (u ij.2)))ᶜ))
    (hZ : Z = (Finset.univ.filter (fun i : Fin p => i.val < p - 1)).inf
        (fun i => Hs (S.erase (u i)))) :
    ∃ e ∈ H.edges, Meets e W ∧ Meets e Z ∧ e ⊆ W ∪ Z := by sorry

end CutSetEnum
