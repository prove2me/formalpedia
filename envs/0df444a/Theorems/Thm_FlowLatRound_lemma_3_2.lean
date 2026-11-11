-- Prove2me | Theorems.Thm_FlowLatRound_lemma_3_2
-- name    : FlowLatRound.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:11.381414+00:00
-- url     : https://prove2.me/theorems/c738b290-b3cf-4f70-a64d-e5a49bb9673b
-- title:
--   Lemma 3.2 — the flow cell: $\mathrm{Vor}(\Lambda_G)=P_G[-\frac12,\frac12]^m$, $V(K_G)=\det\Lambda_G=\sqrt{\tau(G)}$, $\frac{\sqrt d}{2}\le R(K_G)\le\frac{\sqrt m}{2}$
-- statement:
--   Let $G$ be a connected multigraph with $n$ vertices, $m$ edges and cycle rank $d=m-n+1$. Then:
--
--   1. the Voronoi cell of the flow lattice is the zonotope $K_G=P_G[-\tfrac12,\tfrac12]^m$;
--   2. its volume in $H_G$ is $V(K_G)=\sqrt{\tau(G)}$, and it equals $\det\Lambda_G=\sqrt{\det(B^{\top}B)}$ for every basis $B$ of $\Lambda_G$;
--   3. its circumradius satisfies
--   $$\frac{\sqrt d}{2}\le R(K_G)\le\frac{\sqrt m}{2};$$
--   4. $R(K_G)=\sqrt m/2$ whenever all degrees of $G$ are even.
--
--   The cell is explicit, which is what makes $\Phi$ computable for flow lattices.
--
--   Differences from the source:
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
--   - encoding: H_G = ker A_G with one vertex row of the incidence matrix deleted → kernel of the full n×m incidence map; reason: the rows of the full matrix sum to zero, so both kernels are equal
--   - encoding: volume V and surface area S of a convex body in H_G → Lebesgue measure in orthonormal coordinates of H_G (cellVol) and the Minkowski content lim_{s↓0}(V(K_s)−V(K))/s (cellSurf); reason: basis-independent normalization of Lebesgue measure; the Minkowski content equals the surface area of a convex body (Steiner formula, used in the proof of Lemma B.2)
--   - encoding: G connected → 0 < τ(G); reason: a multigraph is connected iff it has a spanning tree
--   - encoding: det Λ_G → √det(BᵀB) for every ℤ-basis B of Λ_G; reason: the covolume of a lattice in terms of any basis
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma 3.2, p.6 (PDF 8); proof p.23 (PDF 25)

import Mathlib
import Definitions.Def_FlowLatRound_FlowGraph

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma 3.2, p.6 (PDF 8); proof p.23 (PDF 25). The flow cell: for a connected
multigraph `G` (`τ(G) > 0`) with cycle rank `d = m − n + 1`, the Voronoi cell of `Λ_G` is the
zonotope `K_G = P_G[−½, ½]^m`; its volume is `√τ(G)` and equals `det Λ_G = √det(BᵀB)` for every
`ℤ`-basis `B` of `Λ_G`; `√d/2 ≤ R(K_G) ≤ √m/2`; and `R(K_G) = √m/2` if all degrees are even.

**Formalization Note.** Volume is taken inside `H_G` (`cellVol` on the subspace); `det Λ_G` is
written as `√det(BᵀB)` for an arbitrary basis `B`. A loop adds `2` to the degree. -/
theorem lemma_3_2 {n m : ℕ} (G : MGraph n m) (hG : 0 < G.tau) :
    G.voronoiG = G.zonotope ∧
    cellVol G.voronoiG = Real.sqrt (G.tau : ℝ) ∧
    (∀ (k : ℕ) (B : Fin m → Fin k → ℤ), IsZBasis G.flowLattice B →
      cellVol G.voronoiG = Real.sqrt (gram B).det) ∧
    Real.sqrt ((m : ℝ) + 1 - n) / 2 ≤ circumradius G.voronoiG ∧
    circumradius G.voronoiG ≤ Real.sqrt (m : ℝ) / 2 ∧
    ((∀ v, Even (G.deg v)) → circumradius G.voronoiG = Real.sqrt (m : ℝ) / 2) := by sorry

end FlowLatRound
