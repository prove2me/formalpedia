-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinManyPotential_nonneg
-- name    : BookProof.VielbeinFock.vielbeinManyPotential_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:23.845761+00:00
-- url     : https://prove2.me/theorems/85f565ab-8c60-436b-a65e-769c884503b6
-- title:
--   `BookProof.VielbeinFock.vielbeinManyPotential_nonneg` {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinManyPotential_nonneg` {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alpha d om n x
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinManyPotential_nonneg`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinManyPotential_nonneg
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

theorem BookProof.VielbeinFock.vielbeinManyPotential_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ)
    (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) :
    0 ≤ vielbeinManyPotential M alpha d om n x := by sorry
