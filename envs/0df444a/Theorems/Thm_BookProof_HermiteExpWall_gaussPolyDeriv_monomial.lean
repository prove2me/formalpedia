-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_gaussPolyDeriv_monomial
-- name    : BookProof.HermiteExpWall.gaussPolyDeriv_monomial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:12:24.037224+00:00
-- url     : https://prove2.me/theorems/dca658ba-83b2-4baa-8bf1-35616358deb7
-- title:
--   `BookProof.HermiteExpWall.gaussPolyDeriv_monomial` (m : ℕ) : gaussPolyDeriv ((Polynomial.X : Polynomial ℝ) ^ (m + 2)) = Polynomial.C ((m : ℝ) + 2) * Polynomial.X ^ (m + 1) - Polyno
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.gaussPolyDeriv_monomial` (m : ℕ) : gaussPolyDeriv ((Polynomial.X : Polynomial ℝ) ^ (m + 2)) = Polynomial.C ((m : ℝ) + 2) * Polynomial.X ^ (m + 1) - Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ (m + 3)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.gaussPolyDeriv_monomial`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.gaussPolyDeriv_monomial
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.gaussPolyDeriv_monomial (m : ℕ) :
    gaussPolyDeriv ((Polynomial.X : Polynomial ℝ) ^ (m + 2))
      = Polynomial.C ((m : ℝ) + 2) * Polynomial.X ^ (m + 1)
        - Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ (m + 3) := by sorry
