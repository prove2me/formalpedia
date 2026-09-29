-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_coreEquiv_symm_pgLp
-- name    : BookProof.QgHermiteFriedrichs.coreEquiv_symm_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:03:56.588074+00:00
-- url     : https://prove2.me/theorems/bc1fd919-498c-4fa2-bb44-49c4620de0a6
-- title:
--   The Lean 4 theorem `coreEquiv_symm_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreEquiv_symm_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.coreEquiv_symm_pgLp
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.coreEquiv_symm_pgLp (p : MvPolynomial (Fin d) ℂ) :
    coreEquiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by sorry
