-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_mem_flipGraph_iff
-- name    : BookProof.FriedrichsSquare.mem_flipGraph_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:40:12.302474+00:00
-- url     : https://prove2.me/theorems/03084915-8309-4297-aab6-d06c3cf760b5
-- title:
--   `BookProof.FriedrichsSquare.mem_flipGraph_iff` {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} : p ∈ flipGraph A ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ clGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.mem_flipGraph_iff` {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} : p ∈ flipGraph A ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ clGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.mem_flipGraph_iff`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.mem_flipGraph_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.mem_flipGraph_iff {A : D →ₗ[ℂ] F} {p : WithLp 2 (F × F)} :
    p ∈ flipGraph A ↔ ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ clGraph A := by sorry
