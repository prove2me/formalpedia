-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqOp_hermiteCore
-- name    : BookProof.FullQuadratic.fqOp_hermiteCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T13:49:31.677643+00:00
-- url     : https://prove2.me/theorems/f76dfce5-533f-4fa5-84d8-1d28a07e2655
-- title:
--   `BookProof.FullQuadratic.fqOp_hermiteCore` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) : fqOp P Q S b b' (hermiteCore a) = ((fqSymbol P Q : ℝ) : ℂ) •...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqOp_hermiteCore` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) : fqOp P Q S b b' (hermiteCore a) = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMvLp a + (∑ i, ∑ j, ((fqAmp P Q S i j * ((rcp a i j : ℝ) : ℂ)) • hermiteMvLp (a + pvec i j) + ((starRingEnd ℂ) (fqAmp P Q S i j) * ((lcp a i j : ℝ) : ℂ)) • hermiteMvLp (a - pvec i j) + (fqExch P Q S i j * ((rcm a i j : ℝ) : ℂ)) • hermiteMvLp (shiftm a i j))) + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)) • hermiteMvLp (a + Finsupp.single i 1) + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)) • hermiteMvLp (a - Finsupp.single i 1))
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqOp_hermiteCore`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_hermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2
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

theorem BookProof.FullQuadratic.fqOp_hermiteCore (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    fqOp P Q S b b' (hermiteCore a)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMvLp a
        + (∑ i, ∑ j, ((fqAmp P Q S i j * ((rcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (a + pvec i j)
                + ((starRingEnd ℂ) (fqAmp P Q S i j) * ((lcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (a - pvec i j)
                + (fqExch P Q S i j * ((rcm a i j : ℝ) : ℂ))
                    • hermiteMvLp (shiftm a i j)))
        + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                  • hermiteMvLp (a + Finsupp.single i 1)
                + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                  • hermiteMvLp (a - Finsupp.single i 1)) := by sorry
