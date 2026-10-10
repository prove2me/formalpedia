-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConf_hasZeroDeficiencyOn
-- name    : BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:19.261846+00:00
-- url     : https://prove2.me/theorems/cdf74b8d-6808-4103-aed1-c94fce377e44
-- title:
--   `BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn` : HasZeroDeficiencyOn (densConfCore M alpha) (densConfOp M alpha)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn` : HasZeroDeficiencyOn (densConfCore M alpha) (densConfOp M alpha)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn
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

theorem BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn (densConfCore M alpha) (densConfOp M alpha) := by sorry
