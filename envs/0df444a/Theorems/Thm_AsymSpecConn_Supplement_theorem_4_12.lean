-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_4_12
-- name    : AsymSpecConn.Supplement.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:27:56.776174+00:00
-- url     : https://prove2.me/theorems/9750f481-00e2-4c8f-a151-ed9e78a87ab6
-- title:
--   Theorem 4.12 — graph-edge spectra are star-convex from incidence vectors
-- statement:
--   Let $K$ be a field, let $k\ge2$, and let $H$ be a simple graph with vertex set $[k]$ and edge set $E$. For each $e\in E$, let $b_e$ be its edge tensor. Then
--
--   $$
--   \log\Delta_K((b_e)_{e\in E})
--   $$
--
--   is star-convex with respect to every point of $\operatorname{conv}\{\chi_w:w\in[k]\}$, where $\chi_w$ is the edge-incidence vector of vertex $w$.
--
--   Every vertex is included, so an isolated vertex contributes the zero incidence vector.
--
--   Differences from the source:
--   - encoding: the coordinates are indexed by unoriented graph edges → each edge is represented once by its increasing ordered pair of endpoints; reason: this is a bijective finite index representation and changes no tensor or incidence-vector value
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Definition 4.11 and Theorem 4.12, p.36

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_graphGenerator

set_option autoImplicit false

namespace AsymSpecConn.Supplement

universe u

/-- **Theorem 4.12** (p.36) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): for every field and every finite simple graph on `k ≥ 2` vertices,
the logarithmic joint spectrum of its edge generators is star-convex from every point of the
convex hull of all vertex-incidence vectors.

**Formalization Note** Edges are uniquely oriented by increasing endpoint only to index the
coordinates. Every vertex is retained in the convex hull, including isolated vertices whose
incidence vector is zero. -/
theorem theorem_4_12 (K : Type u) [Field K] {k : ℕ} (hk : 2 ≤ k)
    (H : SimpleGraph (Fin k)) :
    StarConvexWith
      (logValueSet (AsymSpecConn.tensorPreorder K hk) (graphGenerator K H))
      (convexHull ℝ (Set.range (incidenceVector H))) := by sorry

end AsymSpecConn.Supplement
