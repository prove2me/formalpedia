-- Prove2me | Theorems.Thm_FlowLatRound_proposition_3_3
-- name    : FlowLatRound.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:11.400037+00:00
-- url     : https://prove2.me/theorems/1981d2b8-4d47-44e2-8865-798cdda094f8
-- title:
--   Proposition 3.3 — surface area via fundamental cycles: $\frac{S(K_G)}{V(K_G)}=\frac{2}{\tau(G)}\sum_{F\in U(G)}\sqrt{\ell(F)}=2\,\mathbb E_{T}\sum_{e\notin T}|C(T,e)|^{-1/2}\le 2d$
-- statement:
--   Let $G$ be a connected multigraph with cycle rank $d\ge2$, $U(G)$ the set of connected spanning subgraphs with exactly $n$ edges, and $\ell(F)$ the length of the unique cycle of $F\in U(G)$. Then
--   $$\frac{S(K_G)}{V(K_G)}=\frac{2}{\tau(G)}\sum_{F\in U(G)}\sqrt{\ell(F)}=2\,\mathbb E_{T\sim\mathrm{UST}(G)}\sum_{e\notin T}|C(T,e)|^{-1/2},\tag{4}$$
--   and in particular $S(K_G)/V(K_G)\le2d$.
--
--   This turns the boundary of the cell into a statistic of fundamental cycles of a uniform spanning tree.
--
--   Differences from the source:
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
--   - encoding: H_G = ker A_G with one vertex row of the incidence matrix deleted → kernel of the full n×m incidence map; reason: the rows of the full matrix sum to zero, so both kernels are equal
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: G connected → 0 < τ(G); reason: a multigraph is connected iff it has a spanning tree
--   - encoding: U(G), ℓ(F), |C(T,e)|, E over UST(G) → edge sets with the cut-connectivity condition; ℓ(F) and |C(T,e)| as numbers of edges whose removal leaves a spanning tree; the average over the τ(G) spanning trees; reason: standard characterizations of the cycle of a unicyclic graph and of the uniform law
--   - encoding: d ≥ 2 → n + 2 ≤ m + 1; reason: d = m − n + 1 without natural subtraction
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Proposition 3.3, Eq. (4), p.6 (PDF 8); proof p.22 (PDF 24)

import Mathlib
import Definitions.Def_FlowLatRound_FlowGraph

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Proposition 3.3, Eq. (4), p.6 (PDF 8); proof p.22 (PDF 24). Surface area via fundamental
cycles: for a connected multigraph `G` with cycle rank `d ≥ 2`,
`S(K_G)/V(K_G) = (2/τ(G)) Σ_{F ∈ U(G)} √ℓ(F) = 2 E_{T∼UST(G)} Σ_{e∉T} |C(T,e)|^{−1/2}`, and
`S(K_G)/V(K_G) ≤ 2d`.

**Formalization Note.** `d ≥ 2` is written `n + 2 ≤ m + 1`; `E_{T∼UST(G)}` is the average over
the `τ(G)` spanning trees. -/
theorem proposition_3_3 {n m : ℕ} (G : MGraph n m) (hG : 0 < G.tau) (hd : n + 2 ≤ m + 1) :
    cellSurf G.voronoiG / cellVol G.voronoiG =
      2 / (G.tau : ℝ) * ∑ F ∈ G.unicyclic, Real.sqrt (G.ellF F : ℝ) ∧
    cellSurf G.voronoiG / cellVol G.voronoiG =
      2 * ((1 / (G.tau : ℝ)) * ∑ T ∈ G.spanningTrees,
        ∑ e ∈ Finset.univ.filter (fun e => e ∉ T), (G.cycLen T e : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    cellSurf G.voronoiG / cellVol G.voronoiG ≤ 2 * ((m : ℝ) + 1 - n) := by sorry

end FlowLatRound
