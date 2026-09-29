-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_sirkDen_rkVec
-- name    : BookProof.HashimotoShiftInvert.sirkDen_rkVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:15.389898+00:00
-- url     : https://prove2.me/theorems/b987851a-5d5d-45e8-bb89-691c156042b1
-- title:
--   The Lean 4 theorem `sirkDen_rkVec` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirkDen_rkVec` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.sirkDen_rkVec
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.sirkDen_rkVec {A : Dom →ₗ[ℂ] F} {γ : ℕ → ℂ} {X : ℕ → F →L[ℂ] F} (m : ℕ)
    (hX : ∀ j, IsShiftInvertC A (γ j) (X j)) (v : F) (k : ℕ) :
    sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v := by sorry
