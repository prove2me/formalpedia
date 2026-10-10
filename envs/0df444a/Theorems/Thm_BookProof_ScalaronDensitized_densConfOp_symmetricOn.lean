-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConfOp_symmetricOn
-- name    : BookProof.ScalaronDensitized.densConfOp_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:21.017995+00:00
-- url     : https://prove2.me/theorems/ffad362c-d02d-48c9-a19e-489676f50560
-- title:
--   `BookProof.ScalaronDensitized.densConfOp_symmetricOn` : SymmetricOn (densConfCore M alpha) ((densConfCore M alpha).subtype.comp (densConfOp M alpha))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConfOp_symmetricOn` : SymmetricOn (densConfCore M alpha) ((densConfCore M alpha).subtype.comp (densConfOp M alpha))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConfOp_symmetricOn`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConfOp_symmetricOn
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

theorem BookProof.ScalaronDensitized.densConfOp_symmetricOn :
    SymmetricOn (densConfCore M alpha)
      ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) := by sorry
