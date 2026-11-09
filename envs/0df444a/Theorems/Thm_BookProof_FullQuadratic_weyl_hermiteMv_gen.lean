-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_weyl_hermiteMv_gen
-- name    : BookProof.FullQuadratic.weyl_hermiteMv_gen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:28:42.370115+00:00
-- url     : https://prove2.me/theorems/4ae8a369-84b4-41f2-b91a-c7e909f91a25
-- title:
--   `BookProof.FullQuadratic.weyl_hermiteMv_gen` (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (lop t i) (lop t' j) (hermiteMv a) = hermiteMv (a + pve
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.weyl_hermiteMv_gen` (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (lop t i) (lop t' j) (hermiteMv a) = hermiteMv (a + pvec i j) + (t * (a i : ℂ)) • hermiteMv (shiftm a j i) + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j) + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j) + (if i = j then ((t + t') / 2) • hermiteMv a else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.weyl_hermiteMv_gen`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.weyl_hermiteMv_gen
import Definitions.Def_ChapterHermiteProductBasis
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
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
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

theorem BookProof.FullQuadratic.weyl_hermiteMv_gen (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (lop t i) (lop t' j) (hermiteMv a)
      = hermiteMv (a + pvec i j)
        + (t * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
            • hermiteMv (a - pvec i j)
        + (if i = j then ((t + t') / 2) • hermiteMv a else 0) := by sorry
