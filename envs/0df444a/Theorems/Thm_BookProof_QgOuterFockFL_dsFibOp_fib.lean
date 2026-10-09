-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_fib
-- name    : BookProof.QgOuterFockFL.dsFibOp_fib
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:23:23.055596+00:00
-- url     : https://prove2.me/theorems/ba866954-31bb-4acc-87e7-28f19af57586
-- title:
--   The Lean 4 theorem `dsFibOp_fib` in the `ChapterQgOuterFockFarisLavine` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QgOuterFockFL.dsFibOp_fib` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.dsFibOp_fib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.QgOuterFockFL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}


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

theorem BookProof.QgOuterFockFL.dsFibOp_fib {K : ℝ}
    (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖)
    (x : dsDom C) (i : ι) :
    ((dsFibOp C H K hrel x : lp G 2) : ∀ i, G i) i = H i (fib C x i) := by sorry
