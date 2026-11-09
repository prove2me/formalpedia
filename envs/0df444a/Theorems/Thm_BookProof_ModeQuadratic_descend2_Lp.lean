-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_descend2_Lp
-- name    : BookProof.ModeQuadratic.descend2_Lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:37:52.734038+00:00
-- url     : https://prove2.me/theorems/51253386-23dc-405f-9db5-291c890f8981
-- title:
--   `BookProof.ModeQuadratic.descend2_Lp` (i : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • ((c * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • pgLp (hermiteMv (a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.descend2_Lp` (i : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • ((c * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • pgLp (hermiteMv (a - Finsupp.single i 2))) = (c * ((lc2 a i : ℝ) : ℂ)) • hermiteMvLp (a - Finsupp.single i 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.descend2_Lp`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.descend2_Lp
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

theorem BookProof.ModeQuadratic.descend2_Lp (i : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ •
        ((c * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • pgLp (hermiteMv (a - Finsupp.single i 2)))
      = (c * ((lc2 a i : ℝ) : ℂ)) • hermiteMvLp (a - Finsupp.single i 2) := by sorry
