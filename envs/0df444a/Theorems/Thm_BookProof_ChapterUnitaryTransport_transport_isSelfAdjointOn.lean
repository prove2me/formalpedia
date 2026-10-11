-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryTransport_transport_isSelfAdjointOn
-- name    : BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:49:28.063982+00:00
-- url     : https://prove2.me/theorems/2280d71c-0bab-45f9-b177-46a1a5421d52
-- title:
--   `BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn` (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : IsSelfAdjointOn D A) : IsSelfAdjointOn (transportDomain W D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryTransport`.
--
--   `BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn` (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : IsSelfAdjointOn D A) : IsSelfAdjointOn (transportDomain W D) (transportOp W D A)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn`.

-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hA : IsSelfAdjointOn D A) :
    IsSelfAdjointOn (transportDomain W D) (transportOp W D A) := by sorry
