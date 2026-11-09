-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_lemma_4_3
-- name    : DirectedGlobalMincut.Sampling.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:44.607347+00:00
-- url     : https://prove2.me/theorems/c36c634b-bcd6-4a7a-88ab-01e64ccb225a
-- title:
--   Lemma 4.3 — Compression preserves every flow projection
-- statement:
--   Fix a spanning out-arborescence $T$ rooted at $r$, a nonnegative real vector $q$, and any prescribed original-edge vector $h$. Write $H_T$ for the warmup network and $H'_T$ for its explicit heavy-light/segment-tree compression. Then
--
--   $$\exists g\text{ feasible in }H'_T:\ g|_E=h
--   \quad\Longleftrightarrow\quad
--   \exists g_0\text{ feasible in }H_T:\ g_0|_E=h.$$
--
--   Both flows must satisfy the specified demands. The same projection is preserved in both directions, so the compression can replace the larger network in the support-mixing computation.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n vertices and an ambient Fin m arc type, with G.arcs selecting the active identities; reason: all source graphs have an exhaustive enumeration; unused ambient identifiers have zero incidence and zero auxiliary projection, so permitting them changes no active graph or cut
--   - encoding: a_e=(s_v,y_e) for every e=(u,v), although s_r is not defined on p.5 → omit source arcs entering r and project those original arcs to zero; reason: every rooted out-arborescence already has zero incidence on these arcs; the two-vertex opposite-arcs graph demonstrates the undefined source symbol
--   - reading: in each case with g|E=g0|E → for every prescribed h, a feasible lift exists in one network iff a feasible lift exists in the other; reason: the p.8 proof translates each given flow while retaining the source-arc values, so unrelated existential flows would omit the assertion
--   - reading: a standard heavy-light decomposition and segment trees → heavy edges use the half-subtree threshold, with balanced segment nodes and their maximal contained cover; reason: this fixes a standard valid heavy-light convention without changing either projection fiber
--   - generalization: G subject to the global input restrictions of section 1 → the structural assertion on any finite arc-identity digraph with a spanning out-arborescence; reason: the displayed assertions and their source proofs do not use weights, polynomial bounds or m>=n; all original instances are included
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Lemma 4.3, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Compression

open Classical

namespace DirectedGlobalMincut.Sampling

/-- Lemma 4.3 (p.8): equality of projection fibers in both directions. -/
theorem lemma_4_3 {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (hT : IsTree G r T) (q : Fin m → ℝ) (hq : ∀ e, 0 ≤ q e) (h : Fin m → ℝ) :
    (∃ g, FeasibleFlow (compressedNetwork G r T q) g ∧ compressedProjection G r T g = h) ↔
      (∃ g, FeasibleFlow (warmNetwork G r T q) g ∧ warmProjection G r T g = h) := by sorry

end DirectedGlobalMincut.Sampling
