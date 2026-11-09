-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_3
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:33:18.67462+00:00
-- url     : https://prove2.me/theorems/30bfbdb0-7dfb-4a06-aba7-4c08de7c41b5
-- title:
--   Lemma 4.3 — Algorithm 1 restores exact distances after a distance-decreasing update
-- statement:
--   Let the data structure be in any reachable state for the graph $G$ and source $s$ (initialized on some graph and updated by any sequence of requests), with arbitrary nonnegative real weights. Apply a distance-decreasing request: an insertion of an absent arc $u\to v$ ($u\ne v$) or a strict decrease of the weight of a present arc. Let $G'$ be the updated graph. Then Algorithm 1 — propagation starting from the head $v$ — processes exactly the affected vertices,
--   $$V'=\{x : d_{G'}(s,x)<d_G(s,x)\},$$
--   and afterwards every label is the exact post-update distance: $d_x=d_{G'}(s,x)$ for all $x$ (affected vertices are recomputed, all other labels keep their exact values).
--
--   Differences from the source:
--   - reading: 'propagation starting from the head vertex v … and restricted to the affected region computes the exact post-update shortest-path distances of all affected vertices' → the processed set of Algorithm 1 equals the affected set A, and every label equals the exact post-update distance; reason: 'restricted to the affected region' describes the processed set; unaffected vertices keep their already exact labels, as the lemma's proof and §3.3 state
--   - encoding: indexed edge and heap handles, adjacency lists, tree-child links, cached degrees and preferred incoming-record minima in the pointer-operation cost model → maps and lists specify pointer-structure contents extensionally; the cost counts their source operations, and processed/scanned sets are ghost observations; reason: map updates denote handle writes, erase denotes unlinking a known handle, adjacency and subtree enumerations charge their visited entries, and heap scans/links/promotions are charged explicitly; costs describe the source pointer program, not evaluation of the functional Lean representation
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.3, PDF p.6 = printed p.6; Algorithm 1, PDF p.4; Appendix A.1, PDF p.14

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Algorithm

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.3 (PDF p. 6). For a distance-decreasing request (insertion of an absent arc or a
strict weight decrease) applied to any state of the data structure, Algorithm 1 — propagation
from the head `v`, processing exactly the affected vertices (those whose distance strictly
decreases) — leaves every label equal to the exact post-update distance. -/
theorem lemma_4_3 {n : ℕ} (G : WDigraph n) (s : Fin n) (ds : DS n)
    (hds : IsReachableState G s ds) (upd : Update n) (hdec : upd.IsDecreasing G) :
    (∀ x, (applyUpdate ds upd).ds.d x = (upd.applyTo G).dist s x) ∧
    (applyUpdate ds upd).processed =
      Finset.univ.filter (fun x => (upd.applyTo G).dist s x < G.dist s x) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
