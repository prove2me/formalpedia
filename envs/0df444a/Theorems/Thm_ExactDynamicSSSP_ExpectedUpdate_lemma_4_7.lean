-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_4_7
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:38.399286+00:00
-- url     : https://prove2.me/theorems/08b4ec03-0fbb-4c3d-9a23-45ba62c9cb9a
-- title:
--   Lemma 4.7 — Algorithm 3 restores exact distances after a distance-increasing update
-- statement:
--   Let the data structure be in any reachable state for $G$ and source $s$, with arbitrary nonnegative real weights, and apply a distance-increasing request to the arc $u\to v$: deletion of a present arc or a strict increase of its weight. Let $G'$ be the updated graph and $\mathrm{par}$ the old certified tree. Then:
--
--   1. boundary initialization followed by minimum-key relaxation within the old subtree $SPT_v$ (Algorithm 3) leaves every label equal to the exact post-update distance, $d_x=d_{G'}(s,x)$ for all $x$;
--   2. if a vertex $y\in V(SPT_v)$ keeps its old distance, so does every vertex $z$ of its old subtree $V(SPT_y)$.
--
--   Differences from the source:
--   - reading: 'If a vertex y retains its old distance, so do all vertices in its old subtree SPT_y' → for every y in the old subtree V(SPT_v) of the updated arc's head; reason: the lemma concerns the recomputation within SPT_v; for y outside it (e.g. y = s) the clause fails whenever a distance changes, and the source's proof appends a tree suffix that avoids u→v, which holds exactly for y ∈ V(SPT_v)
--   - encoding: indexed edge and heap handles, adjacency lists, tree-child links, cached degrees and preferred incoming-record minima in the pointer-operation cost model → maps and lists specify pointer-structure contents extensionally; the cost counts their source operations, and processed/scanned sets are ghost observations; reason: map updates denote handle writes, erase denotes unlinking a known handle, adjacency and subtree enumerations charge their visited entries, and heap scans/links/promotions are charged explicitly; costs describe the source pointer program, not evaluation of the functional Lean representation
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 4.7, PDF p.7 = printed p.7; Algorithm 3 and its correctness proof, Appendix A.2, PDF pp.14–15

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Algorithm

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 4.7 (PDF p. 7). For a distance-increasing request (deletion of a present arc or a
strict weight increase) of the arc `u → v` applied to any state of the data structure,
Algorithm 3 (boundary initialization followed by minimum-key relaxation within the old subtree
`SPT_v`) leaves every label equal to the exact post-update distance. Moreover, if a vertex `y`
of the old subtree `V(SPT_v)` keeps its distance, so does every vertex of its old subtree
`V(SPT_y)`. -/
theorem lemma_4_7 {n : ℕ} (G : WDigraph n) (s : Fin n) (ds : DS n)
    (hds : IsReachableState G s ds) (upd : Update n) (hinc : upd.IsIncreasing G) :
    (∀ x, (applyUpdate ds upd).ds.d x = (upd.applyTo G).dist s x) ∧
    (∀ y ∈ subtree s ds.par upd.arc.2, (upd.applyTo G).dist s y = G.dist s y →
      ∀ z ∈ subtree s ds.par y, (upd.applyTo G).dist s z = G.dist s z) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
