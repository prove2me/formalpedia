-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_isInv_of_rho
-- name    : BookProof.ChapterWeylSL2Group.isInv_of_rho
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:39:03.277597+00:00
-- url     : https://prove2.me/theorems/e8e1fb78-0054-4fb8-8907-4a6dc18d3074
-- title:
--   `BookProof.ChapterWeylSL2Group.isInv_of_rho` (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W) (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.isInv_of_rho` (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W) (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W) : R.IsInv W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.isInv_of_rho`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.isInv_of_rho
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem BookProof.ChapterWeylSL2Group.isInv_of_rho (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W) : R.IsInv W := by sorry
