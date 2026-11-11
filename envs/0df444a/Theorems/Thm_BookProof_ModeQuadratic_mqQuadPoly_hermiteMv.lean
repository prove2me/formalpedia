-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_mqQuadPoly_hermiteMv
-- name    : BookProof.ModeQuadratic.mqQuadPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:37:10.75474+00:00
-- url     : https://prove2.me/theorems/84a0c8bc-9b90-4c3a-b5aa-afc0df085cb6
-- title:
--   `BookProof.ModeQuadratic.mqQuadPoly_hermiteMv` (p q s : Fin d → ℝ) (a : Fin d →₀ ℕ) : mqQuadPoly p q s (hermiteMv a) = ((mqSymbol p q a : ℝ) : ℂ) • hermiteMv a + ∑ i, (mqAmp p q s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.mqQuadPoly_hermiteMv` (p q s : Fin d → ℝ) (a : Fin d →₀ ℕ) : mqQuadPoly p q s (hermiteMv a) = ((mqSymbol p q a : ℝ) : ℂ) • hermiteMv a + ∑ i, (mqAmp p q s i • hermiteMv (a + Finsupp.single i 2) + ((starRingEnd ℂ) (mqAmp p q s i) * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.mqQuadPoly_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.mqQuadPoly_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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

theorem BookProof.ModeQuadratic.mqQuadPoly_hermiteMv (p q s : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    mqQuadPoly p q s (hermiteMv a)
      = ((mqSymbol p q a : ℝ) : ℂ) • hermiteMv a
        + ∑ i, (mqAmp p q s i • hermiteMv (a + Finsupp.single i 2)
              + ((starRingEnd ℂ) (mqAmp p q s i) * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ)))
                  • hermiteMv (a - Finsupp.single i 2)) := by sorry
