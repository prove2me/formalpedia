-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqQuadPoly_hermiteMv
-- name    : BookProof.FullQuadratic.fqQuadPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T13:48:54.739494+00:00
-- url     : https://prove2.me/theorems/7ef6486d-04ae-46f6-b67d-335aabe3ac20
-- title:
--   `BookProof.FullQuadratic.fqQuadPoly_hermiteMv` (P Q S : Fin d → Fin d → ℝ) (a : Fin d →₀ ℕ) : fqQuadPoly P Q S (hermiteMv a) = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a + ∑ i,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqQuadPoly_hermiteMv` (P Q S : Fin d → Fin d → ℝ) (a : Fin d →₀ ℕ) : fqQuadPoly P Q S (hermiteMv a) = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a + ∑ i, ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j) + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j) + (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j))
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqQuadPoly_hermiteMv`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqQuadPoly_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
open BookProof.FullQuadratic
open BookProof.CarlemanSimplex



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.fqQuadPoly_hermiteMv (P Q S : Fin d → Fin d → ℝ) (a : Fin d →₀ ℕ) :
    fqQuadPoly P Q S (hermiteMv a)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a
        + ∑ i, ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j)
            + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
                * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
                  • hermiteMv (a - pvec i j)
            + (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)) := by sorry
