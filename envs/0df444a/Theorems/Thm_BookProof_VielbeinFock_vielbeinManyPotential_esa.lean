-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinManyPotential_esa
-- name    : BookProof.VielbeinFock.vielbeinManyPotential_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:50:49.215054+00:00
-- url     : https://prove2.me/theorems/6380f438-be5d-47c8-9c61-4f66477c61b6
-- title:
--   `BookProof.VielbeinFock.vielbeinManyPotential_esa` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) : EssentiallySelfAdjointOn (ccDomain (vielbeinSector d n)) (opCc (vielbeinManyPote
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinManyPotential_esa` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) : EssentiallySelfAdjointOn (ccDomain (vielbeinSector d n)) (opCc (vielbeinManyPotential M alpha d om n) (contDiff_vielbeinManyPotential M alpha d om n))
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinManyPotential_esa`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinManyPotential_esa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.VielbeinFock.vielbeinManyPotential_esa (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn (ccDomain (vielbeinSector d n))
      (opCc (vielbeinManyPotential M alpha d om n)
        (contDiff_vielbeinManyPotential M alpha d om n)) := by sorry
