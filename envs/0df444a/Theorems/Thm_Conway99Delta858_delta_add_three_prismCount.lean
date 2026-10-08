-- Prove2me | Theorems.Thm_Conway99Delta858_delta_add_three_prismCount
-- name    : Conway99Delta858.delta_add_three_prismCount
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:14:54.04558+00:00
-- url     : https://prove2.me/theorems/ef3ae519-3a44-414a-aadf-da527b839c45
-- title:
--   Actual-graph delta and prism census identity
-- statement:
--   For every finite graph satisfying SRG(99,14,1,2), the number delta of unordered disjoint triangle pairs joined by two edges plus three times the number of unordered triangular-prism pairs is 4158. The local partner census is proved from the same graph, without an extra premise.
-- source:
--   Committed Opus delta858 Census.lean at 9c021a134a299e87dfebf9caadaa8163847f0215 (proof bytes from 911da8907f8c3681c9849c3e8755b66ed59afda1); frozen GraphCounts.lean and TriangleIncidence.lean dependencies. Private local qualification only.

import Definitions.Def_Conway99_Delta858_20261003
set_option autoImplicit false

theorem Conway99Delta858.delta_add_three_prismCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : Conway99Formal.TriangleBound.delta G + 3 * Conway99Formal.TriangleBound.prismCount G = 4158 := by sorry
