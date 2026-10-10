-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_physConf_esa
-- name    : BookProof.ScalaronDensitized.physConf_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:22:04.203453+00:00
-- url     : https://prove2.me/theorems/cfb7abc2-20de-4f28-908e-293d409d023f
-- title:
--   `BookProof.ScalaronDensitized.physConf_esa` : EssentiallySelfAdjointOn (physConfCore M alpha) ((physConfCore M alpha).subtype.comp (physConfOp M alpha))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.physConf_esa` : EssentiallySelfAdjointOn (physConfCore M alpha) ((physConfCore M alpha).subtype.comp (physConfOp M alpha))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.physConf_esa`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.physConf_esa
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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

theorem BookProof.ScalaronDensitized.physConf_esa :
    EssentiallySelfAdjointOn (physConfCore M alpha)
      ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) := by sorry
