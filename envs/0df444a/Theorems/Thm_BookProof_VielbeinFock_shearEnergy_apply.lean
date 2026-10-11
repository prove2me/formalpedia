-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_shearEnergy_apply
-- name    : BookProof.VielbeinFock.shearEnergy_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:49:54.7172+00:00
-- url     : https://prove2.me/theorems/a9846446-d145-441b-bc06-bc31ce1c0bb2
-- title:
--   `BookProof.VielbeinFock.shearEnergy_apply` (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) (x : vielbeinSector d n) : shearEnergy d om n j x = ∑ i : Fin d, om i ^ 2 / 2 * (x (j, i.cas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.shearEnergy_apply` (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n) (x : vielbeinSector d n) : shearEnergy d om n j x = ∑ i : Fin d, om i ^ 2 / 2 * (x (j, i.castSucc)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.shearEnergy_apply`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.shearEnergy_apply
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

theorem BookProof.VielbeinFock.shearEnergy_apply (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n)
    (x : vielbeinSector d n) :
    shearEnergy d om n j x = ∑ i : Fin d, om i ^ 2 / 2 * (x (j, i.castSucc)) ^ 2 := by sorry
