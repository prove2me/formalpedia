-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_dcommOp_apply
-- name    : BookProof.SmDiracYukawa.dcommOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:53:31.89691+00:00
-- url     : https://prove2.me/theorems/eb26ca31-1f6b-4465-909b-6b683528406e
-- title:
--   `BookProof.SmDiracYukawa.dcommOp_apply` (H N : FermiFock n →ₗ[ℂ] FermiFock n) (ψ : FermiFock n) : dcommOp H N ψ = N (N (H ψ)) - N (H (N ψ)) - (N (H (N ψ)) - H (N (N ψ)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.dcommOp_apply` (H N : FermiFock n →ₗ[ℂ] FermiFock n) (ψ : FermiFock n) : dcommOp H N ψ = N (N (H ψ)) - N (H (N ψ)) - (N (H (N ψ)) - H (N (N ψ)))
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.dcommOp_apply`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.dcommOp_apply
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.dcommOp_apply (H N : FermiFock n →ₗ[ℂ] FermiFock n) (ψ : FermiFock n) :
    dcommOp H N ψ = N (N (H ψ)) - N (H (N ψ)) - (N (H (N ψ)) - H (N (N ψ))) := by sorry
