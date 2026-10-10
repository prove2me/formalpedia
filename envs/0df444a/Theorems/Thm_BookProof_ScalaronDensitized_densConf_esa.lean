-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConf_esa
-- name    : BookProof.ScalaronDensitized.densConf_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:30.490108+00:00
-- url     : https://prove2.me/theorems/1f4adf76-ed50-4a47-809e-d6861fcf5a3e
-- title:
--   `BookProof.ScalaronDensitized.densConf_esa` : EssentiallySelfAdjointOn (densConfCore M alpha) ((densConfCore M alpha).subtype.comp (densConfOp M alpha))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConf_esa` : EssentiallySelfAdjointOn (densConfCore M alpha) ((densConfCore M alpha).subtype.comp (densConfOp M alpha))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConf_esa`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConf_esa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

theorem BookProof.ScalaronDensitized.densConf_esa :
    EssentiallySelfAdjointOn (densConfCore M alpha)
      ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) := by sorry
