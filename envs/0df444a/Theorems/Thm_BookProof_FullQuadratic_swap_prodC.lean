-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_swap_prodC
-- name    : BookProof.FullQuadratic.swap_prodC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:27:11.831559+00:00
-- url     : https://prove2.me/theorems/dcc12b64-d226-41cf-b24e-acacc007c1a5
-- title:
--   `BookProof.FullQuadratic.swap_prodC` (a : Fin d →₀ ℕ) (i j : Fin d) : ((a j : ℂ)) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) = ((a i : ℂ)) * (((a - Finsupp.single i 1 :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.swap_prodC` (a : Fin d →₀ ℕ) (i j : Fin d) : ((a j : ℂ)) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) = ((a i : ℂ)) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.swap_prodC`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.swap_prodC
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

theorem BookProof.FullQuadratic.swap_prodC (a : Fin d →₀ ℕ) (i j : Fin d) :
    ((a j : ℂ)) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)
      = ((a i : ℂ)) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ) := by sorry
