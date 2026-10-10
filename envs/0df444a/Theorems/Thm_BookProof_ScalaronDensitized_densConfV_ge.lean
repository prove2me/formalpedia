-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConfV_ge
-- name    : BookProof.ScalaronDensitized.densConfV_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:20:14.63156+00:00
-- url     : https://prove2.me/theorems/a1d7a855-a64e-4b86-9c95-9ccd8ae7e212
-- title:
--   `BookProof.ScalaronDensitized.densConfV_ge` {M alpha : ℝ} (halpha : 0 < alpha) (y : ℝ) : -(M ^ 4 / (16 * alpha)) ≤ densConfV M alpha y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConfV_ge` {M alpha : ℝ} (halpha : 0 < alpha) (y : ℝ) : -(M ^ 4 / (16 * alpha)) ≤ densConfV M alpha y
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConfV_ge`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConfV_ge
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.ScalaronDensitized.densConfV_ge {M alpha : ℝ} (halpha : 0 < alpha) (y : ℝ) :
    -(M ^ 4 / (16 * alpha)) ≤ densConfV M alpha y := by sorry
