-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_potCore_stone_flow
-- name    : BookProof.ScalaronHermiteEsa.potCore_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:57.987753+00:00
-- url     : https://prove2.me/theorems/43b47a28-86f5-4811-8ef8-fc5b568752fd
-- title:
--   `BookProof.ScalaronHermiteEsa.potCore_stone_flow` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsS
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.potCore_stone_flow` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (potCore W hWc hWb) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.potCore_stone_flow`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.potCore_stone_flow
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteOscillator
open BookProof.StoneBridge
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.potCore_stone_flow {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (potCore W hWc hWb) T.op ∧ IsStoneFlow T U := by sorry
