-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_shearEnergy_nonneg
-- name    : BookProof.VielbeinFock.shearEnergy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:50:25.951975+00:00
-- url     : https://prove2.me/theorems/bc14d6ba-ea44-44ee-9cc7-e5c1341139f5
-- title:
--   `BookProof.VielbeinFock.shearEnergy_nonneg` (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) (x : vielbeinSector d n) : 0 ≤ shearEnergy d om n j x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.shearEnergy_nonneg` (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) (x : vielbeinSector d n) : 0 ≤ shearEnergy d om n j x
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.shearEnergy_nonneg`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.shearEnergy_nonneg
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.VielbeinFock.shearEnergy_nonneg (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n)
    (x : vielbeinSector d n) : 0 ≤ shearEnergy d om n j x := by sorry
