-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_physConfOp_symmetricOn
-- name    : BookProof.ScalaronDensitized.physConfOp_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:05.871032+00:00
-- url     : https://prove2.me/theorems/243cc935-3614-4ed5-bf31-66430dce946e
-- title:
--   `BookProof.ScalaronDensitized.physConfOp_symmetricOn` : SymmetricOn (physConfCore M alpha) ((physConfCore M alpha).subtype.comp (physConfOp M alpha))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.physConfOp_symmetricOn` : SymmetricOn (physConfCore M alpha) ((physConfCore M alpha).subtype.comp (physConfOp M alpha))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.physConfOp_symmetricOn`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.physConfOp_symmetricOn
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
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

theorem BookProof.ScalaronDensitized.physConfOp_symmetricOn :
    SymmetricOn (physConfCore M alpha)
      ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) := by sorry
