-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_closure_rational_polyhedron
-- name    : CombOpt.ChvatalRank.closure_rational_polyhedron
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:42.259088+00:00
-- url     : https://prove2.me/theorems/bf9bfb1d-7104-48e0-bccb-2d220d11850f
-- title:
--   Theorem 6.34 — the closure of a rational polyhedron is a rational polyhedron
-- statement:
--   If $P$ is a rational polyhedron, then $P'$ is also a rational polyhedron.
--
--   Although $P'$ is defined by infinitely many cuts, finitely many suffice, so the iterates $P^{(i)}$ form a sequence of polyhedra.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.34, p. 233 (PDF 241)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolyhedron
import Definitions.Def_CombOpt_ChvatalRank_chvatalClosure

open Matrix

namespace CombOpt.ChvatalRank

/-- **Theorem 6.34.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.34, p. 233 (PDF 241): "If P is a rational polyhedron, then P′ is also a
rational polyhedron." (Schrijver 1980.) -/
theorem closure_rational_polyhedron {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsRationalPolyhedron P) :
    IsRationalPolyhedron (chvatalClosure P) := by sorry

end CombOpt.ChvatalRank
