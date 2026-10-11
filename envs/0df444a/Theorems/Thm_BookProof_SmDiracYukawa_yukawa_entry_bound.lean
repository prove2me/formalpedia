-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_yukawa_entry_bound
-- name    : BookProof.SmDiracYukawa.yukawa_entry_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:28.497979+00:00
-- url     : https://prove2.me/theorems/c6ca587f-3720-4048-b873-40da78c48f36
-- title:
--   `BookProof.SmDiracYukawa.yukawa_entry_bound` {UL V UR D : Matrix (Fin 3) (Fin 3) ℂ} (hUL : IsMixing UL) (hV : IsMixing V) (hUR : IsMixing UR) (hD : ∀ k l, k ≠ l → D k l = 0) (i j :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.yukawa_entry_bound` {UL V UR D : Matrix (Fin 3) (Fin 3) ℂ} (hUL : IsMixing UL) (hV : IsMixing V) (hUR : IsMixing UR) (hD : ∀ k l, k ≠ l → D k l = 0) (i j : Fin 3) : ‖(UL * V.conjTranspose * D * UR.conjTranspose) i j‖ ≤ ∑ k : Fin 3, ‖D k k‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.yukawa_entry_bound`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.yukawa_entry_bound
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

open BookProof.SmOneParticle

theorem BookProof.SmDiracYukawa.yukawa_entry_bound {UL V UR D : Matrix (Fin 3) (Fin 3) ℂ}
    (hUL : IsMixing UL) (hV : IsMixing V) (hUR : IsMixing UR)
    (hD : ∀ k l, k ≠ l → D k l = 0) (i j : Fin 3) :
    ‖(UL * V.conjTranspose * D * UR.conjTranspose) i j‖ ≤ ∑ k : Fin 3, ‖D k k‖ := by sorry
