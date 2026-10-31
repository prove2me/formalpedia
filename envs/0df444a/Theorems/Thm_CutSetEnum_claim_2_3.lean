-- Prove2me | Theorems.Thm_CutSetEnum_claim_2_3
-- name    : CutSetEnum.claim_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:45.458971+00:00
-- url     : https://prove2.me/theorems/c1f6fb35-43a6-4ea4-a3d7-146c503f1198
-- title:
--   Claim 2.3 — $d(H_{S-u_i})=d(U)=d(H_{S-u_i-u_j})$
-- statement:
--   **Setting (proof of Lemma 2.1, p.11).** Let $G=(V,E)$ be a hypergraph, $k\ge2$, and $(U,\bar U)$ a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Let $\mathcal C=\{Q\subseteq V:\ \bar U\subsetneq Q,\ d(Q)\le d(U),\ \delta(Q)\ne\delta(U)\}$ and let $S\subseteq U$ be an inclusion-wise minimal transversal of $\mathcal C$. Suppose, for contradiction, that $S=\{u_1,\dots,u_p\}$ with $p\ge 2k$ distinct vertices. For every non-empty $X\subseteq U$ let $(H_X,\bar H_X)$ be the source minimal minimum $(X,\bar U)$-terminal cut. Write $S-u_i=S\setminus\{u_i\}$ and $S-u_i-u_j=S\setminus\{u_i,u_j\}$.
--
--   **Claim 2.3.** For every $i,j\in[p]$ (including $i=j$),
--   $$
--   d(H_{S-u_i})=d(U)=d(H_{S-u_i-u_j}).
--   $$
--
--   Lemma 2.1 shows that this setting cannot occur; the claim is one step of that proof by contradiction and is posed, as in the paper, inside the setting.
--
--   **Formalization Note** The setting is carried as hypotheses: $S$ is the image of an injective map $u:\{0,\dots,p-1\}\to V$ (0-based indices), $H_X$ is a function `Hs` with `IsSourceMinMinTerminalCut H X Uᶜ (Hs X)` for every non-empty $X\subseteq U$, and $S-u_i$ is `S.erase (u i)`.
--
--   Differences from the source:
--   - encoding: S = {u₁, …, u_p}, p ≥ 2k, indices 1…p → S = image of an injective u : Fin p → V, 2k ≤ p, indices 0…p−1; reason: relabelling of the same p distinct vertices
--   - encoding: (H_X, H̅_X) the source minimal minimum (X, Ū)-terminal cut, for X ⊆ U → a function Hs with IsSourceMinMinTerminalCut H X Uᶜ (Hs X) for every non-empty X ⊆ U; reason: the cut exists and is unique for non-empty X (published source_max_cut); the paper only uses non-empty X
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: the (X, Ū)-terminal cuts behind H_X, 2-partitions with X ⊆ A ⊆ V \ Ū → published IsTerminalCut X Uᶜ A := X ⊆ A ∧ Disjoint A Uᶜ (no separate 2-partition clause), inside IsSourceMinMinTerminalCut; reason: X is non-empty and Ū is non-empty, so the two coincide
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Lemma 2.1, proof, Claim 2.3, p.12 (PDF 13), proof p.13 (PDF 14)

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

/-- **Claim 2.3: `d(H_{S−uᵢ}) = d(U) = d(H_{S−uᵢ−uⱼ})`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Lemma 2.1, proof, Claim 2.3, p.12 (PDF 13;
proof p.13): "For every i, j ∈ [p], we have d(H_{S−u_i}) = d(U) = d(H_{S−u_i−u_j})." (The case
`i = j` is included, as on the page.)

**Formalization Note (the Lemma 2.1 setting).** This claim lives inside the proof of Lemma 2.1,
whose standing hypotheses are carried as binders: `k ≥ 2`; `(U, Uᶜ)` a 2-partition with
`d(U) = OPT_k-cut` (`IsOptKCutValue`); `S` a minimal transversal of the collection `C` inside `U`
(`IsMinTransversal`); the proof's contradiction hypothesis `|S| = p ≥ 2k`, with
`S = {u 0, …, u (p-1)}` for an injective `u : Fin p → V` (0-based indices); and `Hs X`, the
paper's `H_X`, the source minimal minimum `(X, Uᶜ)`-terminal cut for every non-empty `X ⊆ U`.
`S − uᵢ` is `S.erase (u i)` and `S − uᵢ − uⱼ` is `(S.erase (u i)).erase (u j)`. Lemma 2.1 shows
that this setting never occurs; the claim is posed, as in the paper, inside it. -/
theorem claim_2_3
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X)) :
    ∀ i j : Fin p, d H (Hs (S.erase (u i))) = d H U ∧
      d H U = d H (Hs ((S.erase (u i)).erase (u j))) := by sorry

end CutSetEnum
