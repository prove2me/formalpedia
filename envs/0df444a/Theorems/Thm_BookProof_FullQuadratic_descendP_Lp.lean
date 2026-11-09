-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_descendP_Lp
-- name    : BookProof.FullQuadratic.descendP_Lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:31:32.367334+00:00
-- url     : https://prove2.me/theorems/5dd0b9d1-dce7-4841-aac6-a748e5175c62
-- title:
--   `BookProof.FullQuadratic.descendP_Lp` (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • ((c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.descendP_Lp` (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) : ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • ((c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • pgLp (hermiteMv (a - pvec i j))) = (c * ((lcp a i j : ℝ) : ℂ)) • hermiteMvLp (a - pvec i j)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.descendP_Lp`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.descendP_Lp
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

theorem BookProof.FullQuadratic.descendP_Lp (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ •
        ((c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
          • pgLp (hermiteMv (a - pvec i j)))
      = (c * ((lcp a i j : ℝ) : ℂ)) • hermiteMvLp (a - pvec i j) := by sorry
