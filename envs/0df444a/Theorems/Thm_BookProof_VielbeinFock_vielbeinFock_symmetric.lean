-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_symmetric
-- name    : BookProof.VielbeinFock.vielbeinFock_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:50:38.314887+00:00
-- url     : https://prove2.me/theorems/cc78303b-70df-4585-81c8-f91bf093c28d
-- title:
--   `BookProof.VielbeinFock.vielbeinFock_symmetric` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) : SymmetricOn (vielbeinFockCore d) (vielbeinFockHamiltonian M alpha d om)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinFock_symmetric` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) : SymmetricOn (vielbeinFockCore d) (vielbeinFockHamiltonian M alpha d om)
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinFock_symmetric`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinFock_symmetric
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
import Definitions.Def_ChapterFarisLavineCore
open BookProof.VielbeinFock


open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.VielbeinFock.vielbeinFock_symmetric (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) :
    SymmetricOn (vielbeinFockCore d) (vielbeinFockHamiltonian M alpha d om) := by sorry
