-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_potential_ge
-- name    : BookProof.VielbeinFock.vielbeinFock_potential_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:51:37.516553+00:00
-- url     : https://prove2.me/theorems/aaee3678-ea01-45e1-b9fc-87ae3036cb33
-- title:
--   `BookProof.VielbeinFock.vielbeinFock_potential_ge` {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alpha
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinFock_potential_ge` {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alpha d om n x
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinFock_potential_ge`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinFock_potential_ge
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

theorem BookProof.VielbeinFock.vielbeinFock_potential_ge {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ)
    (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alpha d om n x := by sorry
