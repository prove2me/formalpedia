-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma7
-- name    : DirectedHamiltonicity.Main.lemma7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:27.682112+00:00
-- url     : https://prove2.me/theorems/132bc2c1-bf67-49db-9792-0a03eae3d2c2
-- title:
--   Lemma 7 — the directed Matrix–Tree Theorem: $\det L_s(H,p)=\sum_T\prod_{e\in T}p(e)$
-- statement:
--   For every loopless directed multigraph $H$ on a finite vertex set $V$, every map $p:E(H)\to\mathbb F_2[y]$ and every vertex $s\in V$,
--   $$\det L_s(H,p)=\sum_{T}\prod_{e\in T}p(e),$$
--   where $T$ ranges over all out-arborescences of $H$ rooted at $s$ and $L_s(H,p)$ is the incoming Laplacian with row and column $s$ deleted.
--
--   The labels $p$ are arbitrary polynomials, not only monomials, and $H$ may be disconnected (then both sides vanish). For $V=\{s\}$ the empty matrix has determinant $1$ and the empty arborescence contributes $1$. The identity converts Hamiltonian-path sums into determinants in Lemma 8.
--
--   Differences from the source:
--   - encoding: T ranges over all out-arborescences of H rooted at s (spanning trees with all arcs directed away from s) → arc sets T with no arc entering s, exactly one arc of T entering each v ≠ s, and every vertex reachable from s along T; reason: the standard equivalent characterization of a spanning out-arborescence
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.8 / printed p.7, Lemma 7 ([GS95, Section 11])

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs

namespace DirectedHamiltonicity.Main

open Multidigraph

open Polynomial

open Classical in
/-- Lemma 7 (directed Matrix–Tree Theorem), PDF p.8 / printed p.7: for every loopless directed
multigraph `H`, every map `p : E(H) → 𝔽₂[y]` and every vertex `s`,
`det L_s(H, p) = ∑_T ∏_{e ∈ T} p(e)`, the sum over all out-arborescences `T` of `H` rooted at `s`. -/
theorem lemma7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (hH : H.Loopless) (p : E → (ZMod 2)[X]) (s : V) :
    (H.reducedLaplacian p s).det =
      ∑ T ∈ Finset.univ.filter (fun T : Finset E => H.IsOutArborescence s T), ∏ e ∈ T, p e := by sorry

end DirectedHamiltonicity.Main
