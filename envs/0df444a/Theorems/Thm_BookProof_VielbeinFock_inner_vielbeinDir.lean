-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_inner_vielbeinDir
-- name    : BookProof.VielbeinFock.inner_vielbeinDir
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:49:43.38188+00:00
-- url     : https://prove2.me/theorems/1a97a285-f2d9-4b14-93e0-4765f94f4c4c
-- title:
--   `BookProof.VielbeinFock.inner_vielbeinDir` (d n : ℕ) (x : vielbeinSector d n) (j : Fin n) (i : Fin (d + 1)) : (inner ℝ x (vielbeinDir d n j i) : ℝ) = x (j, i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.inner_vielbeinDir` (d n : ℕ) (x : vielbeinSector d n) (j : Fin n) (i : Fin (d + 1)) : (inner ℝ x (vielbeinDir d n j i) : ℝ) = x (j, i)
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.inner_vielbeinDir`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.inner_vielbeinDir
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

theorem BookProof.VielbeinFock.inner_vielbeinDir (d n : ℕ) (x : vielbeinSector d n) (j : Fin n) (i : Fin (d + 1)) :
    (inner ℝ x (vielbeinDir d n j i) : ℝ) = x (j, i) := by sorry
