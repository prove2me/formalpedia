-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_potCore_essentiallySelfAdjoint
-- name    : BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:37.604606+00:00
-- url     : https://prove2.me/theorems/c91c1c3a-d27d-44a0-953e-d0ac24f40d33
-- title:
--   `BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (potCore
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint` {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (potCore W hWc hWb)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteOscillator
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint {W : Vd d → ℝ} (hWc : Continuous W)
    (hWb : ExpBounded W) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (potCore W hWc hWb) := by sorry
