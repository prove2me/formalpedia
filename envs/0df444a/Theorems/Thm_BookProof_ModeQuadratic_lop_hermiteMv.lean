-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_lop_hermiteMv
-- name    : BookProof.ModeQuadratic.lop_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:34:46.350713+00:00
-- url     : https://prove2.me/theorems/4c83bc0b-c5ef-484c-89c5-d100711b2645
-- title:
--   `BookProof.ModeQuadratic.lop_hermiteMv` (t : ℂ) (i : Fin d) (b : Fin d →₀ ℕ) : lop t i (hermiteMv b) = hermiteMv (b + Finsupp.single i 1) + (t * (b i : ℂ)) • hermiteMv (b - Finsupp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.lop_hermiteMv` (t : ℂ) (i : Fin d) (b : Fin d →₀ ℕ) : lop t i (hermiteMv b) = hermiteMv (b + Finsupp.single i 1) + (t * (b i : ℂ)) • hermiteMv (b - Finsupp.single i 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.lop_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.lop_hermiteMv
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.ModeQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ModeQuadratic.lop_hermiteMv (t : ℂ) (i : Fin d) (b : Fin d →₀ ℕ) :
    lop t i (hermiteMv b)
      = hermiteMv (b + Finsupp.single i 1) + (t * (b i : ℂ)) • hermiteMv (b - Finsupp.single i 1) := by sorry
