-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_ascendP_Lp
-- name    : BookProof.FullQuadratic.ascendP_Lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:30:58.380465+00:00
-- url     : https://prove2.me/theorems/9daab513-deb5-4935-85bf-3b538f871608
-- title:
--   `BookProof.FullQuadratic.ascendP_Lp` (i j : Fin d) (a : Fin d →₀ ℕ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv (a + pvec i j)) = ((rcp a i j : ℝ) : ℂ) • hermiteMvLp (a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.ascendP_Lp` (i j : Fin d) (a : Fin d →₀ ℕ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv (a + pvec i j)) = ((rcp a i j : ℝ) : ℂ) • hermiteMvLp (a + pvec i j)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.ascendP_Lp`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.ascendP_Lp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.ascendP_Lp (i j : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv (a + pvec i j))
      = ((rcp a i j : ℝ) : ℂ) • hermiteMvLp (a + pvec i j) := by sorry
