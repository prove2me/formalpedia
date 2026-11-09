-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_crossTerm_stone_flow
-- name    : BookProof.FullQuadratic.crossTerm_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:31:55.809461+00:00
-- url     : https://prove2.me/theorems/84d7b06a-929d-4e5e-8987-c504aaff9384
-- title:
--   `BookProof.FullQuadratic.crossTerm_stone_flow` (S : Fin d → Fin d → ℝ) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (fqOp (d := d) 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.crossTerm_stone_flow` (S : Fin d → Fin d → ℝ) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (fqOp (d := d) 0 0 S 0 0) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.crossTerm_stone_flow`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.crossTerm_stone_flow
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.StoneBridge
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

theorem BookProof.FullQuadratic.crossTerm_stone_flow (S : Fin d → Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (fqOp (d := d) 0 0 S 0 0) T.op ∧ IsStoneFlow T U := by sorry
