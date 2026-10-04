-- Prove2me | Theorems.Thm_Conway99Formal_SpectralRanks_spectral_solution
-- name    : Conway99Formal.SpectralRanks.spectral_solution
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:38:45.24098+00:00
-- url     : https://prove2.me/theorems/501eb8c5-c8b6-41c3-8554-51d9b2a68d3a
-- title:
--   Exact rational spectrum of a hypothetical SRG(99,14,1,2)
-- statement:
--   Let G be one finite simple graph satisfying the strongly regular graph parameters (99,14,1,2), and let A be its rational adjacency matrix in those same vertex coordinates. The graph-derived projector E₋=(27I−9A+J)/63 has rank 44; the shifted adjacency matrix A+4I has rank 55; and A has characteristic polynomial (X−14)(X−3)^54(X+4)^44 over ℚ. These are necessary consequences of the stated graph hypothesis. The theorem constructs no graph and proves no nonexistence result.
-- source:
--   Conway99/Conway99/Core.lean (SHA-256 1d5ecefb2efc22445bc7f494578876c5b25222ba4dda52ab10a5df38ec4feedb); Conway99/Conway99/Claims/C01srgcorealgebra.lean (SHA-256 f602da0e770a10fe6267d2984b6d9c8862ca1c521941eeaec7894d7ced2baa34); archive/clean-start/proof-library.zip, proofs/FOUNDATIONS.md (SHA-256 32127d3ecb9cb533d4a019a1786ee17c84aedff5c8a121a42fc62253301d341c) and proofs/ALGEBRA.md (SHA-256 9800a93ab6644ea592953a7dd2896411304c0a40988e0caa447bc47312c8befd)

import Mathlib
import Definitions.Def_spectral_minus_projector

theorem Conway99Formal.SpectralRanks.spectral_solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2) : (Conway99Formal.SpectralRanks.minusProjector G).rank = 44 ∧ (G.adjMatrix ℚ + 4 • (1 : Matrix V V ℚ)).rank = 55 ∧ (G.adjMatrix ℚ).charpoly = (Polynomial.X - Polynomial.C (14 : ℚ)) * (Polynomial.X - Polynomial.C (3 : ℚ)) ^ 54 * (Polynomial.X + Polynomial.C (4 : ℚ)) ^ 44 := by sorry
