-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_pgLp
-- name    : BookProof.QgHermiteFriedrichs.hamCore_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:08.706987+00:00
-- url     : https://prove2.me/theorems/c07d327d-96f8-45ad-b15b-16724abd253a
-- title:
--   The Lean 4 theorem `hamCore_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hamCore_pgLp
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

theorem BookProof.QgHermiteFriedrichs.hamCore_pgLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = hamPoly W hWc hWb p := by sorry
