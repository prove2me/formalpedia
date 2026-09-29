-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_inner_harmP_re
-- name    : BookProof.GaussCoreQuadBounds.inner_harmP_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:16.053648+00:00
-- url     : https://prove2.me/theorems/97be21b6-728e-43f7-87f1-7f7a9bc9d61a
-- title:
--   (p : MvPolynomial (Fin D) ℂ) : (inner ℂ (pgLp (harmP p)) (pgLp p) : ℂ).re = quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.inner_harmP_re` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.inner_harmP_re
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.QgHermiteOscillator

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.inner_harmP_re (p : MvPolynomial (Fin D) ℂ) :
    (inner ℂ (pgLp (harmP p)) (pgLp p) : ℂ).re
      = quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by sorry
