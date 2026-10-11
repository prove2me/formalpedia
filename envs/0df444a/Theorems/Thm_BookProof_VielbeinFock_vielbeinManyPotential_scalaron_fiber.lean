-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinManyPotential_scalaron_fiber
-- name    : BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:50:21.032985+00:00
-- url     : https://prove2.me/theorems/cbeaab36-e683-42e8-8659-5286cb4f86df
-- title:
--   `BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber` (M alpha : ℝ) (om : Fin 0 → ℝ) (n : ℕ) (x : vielbeinSector 0 n) : vielbeinManyPotential M alpha 0 om n x = ∑ j : Fin n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber` (M alpha : ℝ) (om : Fin 0 → ℝ) (n : ℕ) (x : vielbeinSector 0 n) : vielbeinManyPotential M alpha 0 om n x = ∑ j : Fin n, starobinskyV M alpha (x (j, Fin.last 0))
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber (M alpha : ℝ) (om : Fin 0 → ℝ) (n : ℕ)
    (x : vielbeinSector 0 n) :
    vielbeinManyPotential M alpha 0 om n x
      = ∑ j : Fin n, starobinskyV M alpha (x (j, Fin.last 0)) := by sorry
