-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core
-- name    : BookProof.QgOuterFockFL.harmFried_op_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:45.670669+00:00
-- url     : https://prove2.me/theorems/fd2686e3-60a5-4eb3-b084-6cebef2d733f
-- title:
--   `BookProof.QgOuterFockFL.harmFried_op_core` (d : ℕ) (p : polyGaussCore (d := d)) (h : (p : L2d d) ∈ (harmFried d).dom) : (harmFried d).op ⟨(p : L2d d), h⟩ = harmCore p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.harmFried_op_core` (d : ℕ) (p : polyGaussCore (d := d)) (h : (p : L2d d) ∈ (harmFried d).dom) : (harmFried d).op ⟨(p : L2d d), h⟩ = harmCore p
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.harmFried_op_core`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.harmFried_op_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

theorem BookProof.QgOuterFockFL.harmFried_op_core (d : ℕ) (p : polyGaussCore (d := d))
    (h : (p : L2d d) ∈ (harmFried d).dom) :
    (harmFried d).op ⟨(p : L2d d), h⟩ = harmCore p := by sorry
