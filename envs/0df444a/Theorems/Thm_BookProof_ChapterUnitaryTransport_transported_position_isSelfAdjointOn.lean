-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryTransport_transported_position_isSelfAdjointOn
-- name    : BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:16:40.909006+00:00
-- url     : https://prove2.me/theorems/014e0282-f960-4b8a-9c8d-0c56fd43469d
-- title:
--   `BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn` (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) : IsSelfAdjointOn (transportDomain W (mulDomain f)) (transportOp W (mulDomai
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryTransport`.
--
--   `BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn` (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) : IsSelfAdjointOn (transportDomain W (mulDomain f)) (transportOp W (mulDomain f) (mulOp f))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn`.

-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) :
    IsSelfAdjointOn (transportDomain W (mulDomain f)) (transportOp W (mulDomain f) (mulOp f)) := by sorry
