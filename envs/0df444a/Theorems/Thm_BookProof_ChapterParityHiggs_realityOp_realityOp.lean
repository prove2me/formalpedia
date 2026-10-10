-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_realityOp_realityOp
-- name    : BookProof.ChapterParityHiggs.realityOp_realityOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:24.824273+00:00
-- url     : https://prove2.me/theorems/a57f081a-258b-481b-b25b-6c2ba6c62161
-- title:
--   `BookProof.ChapterParityHiggs.realityOp_realityOp` {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (v : I → ℂ) : realityOp M (realityOp M v) = (M * M.map (starRingEnd ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.realityOp_realityOp` {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (v : I → ℂ) : realityOp M (realityOp M v) = (M * M.map (starRingEnd ℂ)) *ᵥ v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.realityOp_realityOp`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.realityOp_realityOp
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterParityHiggs
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.realityOp_realityOp {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (v : I → ℂ) :
    realityOp M (realityOp M v) = (M * M.map (starRingEnd ℂ)) *ᵥ v := by sorry
