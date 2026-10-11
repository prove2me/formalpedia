-- Prove2me | Theorems.Thm_BookProof_VielbeinFock_vielbeinFock_deficiencyTrivialAt
-- name    : BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:51:49.615614+00:00
-- url     : https://prove2.me/theorems/37d8eefb-ff35-4199-a835-9c198c5085b0
-- title:
--   `BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (vielbeinFockCore d) (vielbeinFockHam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterVielbeinFiberFock`.
--
--   `BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt` (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (vielbeinFockCore d) (vielbeinFockHamiltonian M alpha d om) z
--
--   Formalization note: Lean 4 identifier `BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt`.

-- Generated from ChapterVielbeinFiberFock.lean — theorem BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt
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

theorem BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (vielbeinFockCore d) (vielbeinFockHamiltonian M alpha d om) z := by sorry
