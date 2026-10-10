-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConfV_bddBelow
-- name    : BookProof.ScalaronDensitized.densConfV_bddBelow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:21:07.332979+00:00
-- url     : https://prove2.me/theorems/85cf717b-5353-4913-864d-b9ff516b6cd2
-- title:
--   `BookProof.ScalaronDensitized.densConfV_bddBelow` {M alpha : ℝ} (halpha : 0 < alpha) : BddBelow (Set.range fun y => densConfV M alpha y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConfV_bddBelow` {M alpha : ℝ} (halpha : 0 < alpha) : BddBelow (Set.range fun y => densConfV M alpha y)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConfV_bddBelow`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConfV_bddBelow
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

theorem BookProof.ScalaronDensitized.densConfV_bddBelow {M alpha : ℝ} (halpha : 0 < alpha) :
    BddBelow (Set.range fun y => densConfV M alpha y) := by sorry
