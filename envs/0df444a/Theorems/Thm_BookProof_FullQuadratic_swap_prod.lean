-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_swap_prod
-- name    : BookProof.FullQuadratic.swap_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:26:53.517109+00:00
-- url     : https://prove2.me/theorems/0902cf58-3ff9-4c08-8f70-29300509bb9e
-- title:
--   `BookProof.FullQuadratic.swap_prod` (a : Fin d →₀ ℕ) (i j : Fin d) : (a j) * ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) = (a i) * ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.swap_prod` (a : Fin d →₀ ℕ) (i j : Fin d) : (a j) * ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) = (a i) * ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.swap_prod`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.swap_prod
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem BookProof.FullQuadratic.swap_prod (a : Fin d →₀ ℕ) (i j : Fin d) :
    (a j) * ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i)
      = (a i) * ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) := by sorry
