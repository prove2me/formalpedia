-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_fst_mem_clDom_of_mem_factorRel
-- name    : BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:39:52.492985+00:00
-- url     : https://prove2.me/theorems/85f48a46-22fa-4889-9fff-0ef78c866000
-- title:
--   `BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) : p.1 ∈ clDom A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) : p.1 ∈ clDom A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel
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

theorem BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    p.1 ∈ clDom A := by sorry
