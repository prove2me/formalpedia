-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_weyl_hermiteMv
-- name    : BookProof.ModeQuadratic.weyl_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:36:08.608729+00:00
-- url     : https://prove2.me/theorems/cd5d8263-747d-42e0-9191-944e661b2a6a
-- title:
--   `BookProof.ModeQuadratic.weyl_hermiteMv` (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (lop t i) (lop t' i) (hermiteMv a) = hermiteMv (a + Finsupp.s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.weyl_hermiteMv` (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (lop t i) (lop t' i) (hermiteMv a) = hermiteMv (a + Finsupp.single i 2) + (((t + t') * ((a i : ℂ) + 1) + (t + t') * (a i : ℂ)) / 2) • hermiteMv a + (t * t' * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.weyl_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.weyl_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
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
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
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

theorem BookProof.ModeQuadratic.weyl_hermiteMv (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (lop t i) (lop t' i) (hermiteMv a)
      = hermiteMv (a + Finsupp.single i 2)
        + (((t + t') * ((a i : ℂ) + 1) + (t + t') * (a i : ℂ)) / 2) • hermiteMv a
        + (t * t' * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2) := by sorry
