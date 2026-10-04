-- Prove2me | Theorems.Thm_Conway99Formal_TriangleIncidence_private_progress_20261004
-- name    : Conway99Formal.TriangleIncidence.private_progress_20261004
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:49:06.641769+00:00
-- url     : https://prove2.me/theorems/e9cf2b2d-ba93-4a9c-bd3f-bbb17dadb33d
-- title:
--   Necessary triangle incidence identities for an SRG(99,14,1,2)
-- statement:
--   Let G be a finite strongly regular graph with parameters (99,14,1,2). Its actual three-vertex cliques number 231, exactly seven contain each vertex, and exactly eighteen other cliques meet each fixed clique. If N is the integer incidence matrix of vertices against these literal cliques, then N Nᵀ = 7I + A, where A is G’s adjacency matrix. The overlap count uses B = NᵀN − 3I on the same clique carrier. These are necessary identities; they neither construct such a graph nor prove nonexistence.
-- source:
--   Conway99/Conway99/Core.lean, Line and Obligation; Conway99/Conway99/Claims/C05triangleblocklocal.lean §2; archive/clean-start/proof-library.zip!proofs/FOUNDATIONS.md §1. Same-graph complete proof in formalization/2026-10-03/triangle-incidence/private-progress/Sol_TriangleProgressInline.lean, SHA-256 f2f998583977e68caf7f3a5da7557a755bae6d6c3d77e705b587ecb752caac2b, based on QA-passed lane commit 846b123. Necessary result for the public Conway-99 target, not a resolution.

import Mathlib
open Matrix Finset

theorem Conway99Formal.TriangleIncidence.private_progress_20261004 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    let Tri := {T : Finset V // T ∈ G.cliqueFinset 3};
    let N : Matrix V Tri ℤ := fun v T => if v ∈ T.1 then 1 else 0;
    let B : Matrix Tri Tri ℤ := Nᵀ * N - 3 • 1;
    (G.cliqueFinset 3).card = 231 ∧
    (∀ v : V, (Finset.univ.filter fun T : Tri => v ∈ T.1).card = 7) ∧
    (∀ T : Tri, (Finset.univ.filter fun S : Tri => B S T = 1).card = 18) ∧
    N * Nᵀ = 7 • (1 : Matrix V V ℤ) + G.adjMatrix ℤ := by sorry
