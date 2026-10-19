-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_mem_flipGraph_orthogonal_iff
-- name    : BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:40:20.279734+00:00
-- url     : https://prove2.me/theorems/a413aa3d-803b-4f70-a313-4863f5665746
-- title:
--   `BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff` {A : D →ₗ[ℂ] F} {q : WithLp 2 (F × F)} : q ∈ (flipGraph A)ᗮ ↔ WithLp.ofLp q ∈ adjGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff` {A : D →ₗ[ℂ] F} {q : WithLp 2 (F × F)} : q ∈ (flipGraph A)ᗮ ↔ WithLp.ofLp q ∈ adjGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness
open BookProof.EsaClosure
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff {A : D →ₗ[ℂ] F} {q : WithLp 2 (F × F)} :
    q ∈ (flipGraph A)ᗮ ↔ WithLp.ofLp q ∈ adjGraph A := by sorry
