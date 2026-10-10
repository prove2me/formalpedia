-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_fockSmoothPotential_deficiencyTrivialAt
-- name    : BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:22:51.319981+00:00
-- url     : https://prove2.me/theorems/49ced272-2e6d-40f3-9582-bd0db0661622
-- title:
--   `BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt` (W : ∀ n, E n → ℝ) (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) {z : ℂ} (hz : z.im ≠ 0) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt` (W : ∀ n, E n → ℝ) (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (nestedCore E) (fockSmoothPotentialOp W hW) z
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

theorem BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt (W : ∀ n, E n → ℝ)
    (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (nestedCore E) (fockSmoothPotentialOp W hW) z := by sorry
