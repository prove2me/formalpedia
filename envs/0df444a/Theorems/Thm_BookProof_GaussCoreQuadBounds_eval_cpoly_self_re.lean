-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_eval_cpoly_self_re
-- name    : BookProof.GaussCoreQuadBounds.eval_cpoly_self_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:39:33.795178+00:00
-- url     : https://prove2.me/theorems/7d79a49f-f157-40d3-8a64-e1e96f4e5e3f
-- title:
--   (q : MvPolynomial (Fin D) ℂ) (x : Vd D) : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q)).re = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.eval_cpoly_self_re` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.eval_cpoly_self_re
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.eval_cpoly_self_re (q : MvPolynomial (Fin D) ℂ) (x : Vd D) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q)).re
      = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 := by sorry
