-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_fockSmoothPotential_esa
-- name    : BookProof.ScalaronFock.fockSmoothPotential_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:23:16.274144+00:00
-- url     : https://prove2.me/theorems/4e48730f-fba5-4118-98b5-c3aab90d10ad
-- title:
--   `BookProof.ScalaronFock.fockSmoothPotential_esa` (W : ∀ n, E n → ℝ) (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) : EssentiallySelfAdjointOn (nestedCore E) (fockSmoothPotent
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.fockSmoothPotential_esa` (W : ∀ n, E n → ℝ) (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) : EssentiallySelfAdjointOn (nestedCore E) (fockSmoothPotentialOp W hW)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.fockSmoothPotential_esa`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.fockSmoothPotential_esa
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

theorem BookProof.ScalaronFock.fockSmoothPotential_esa (W : ∀ n, E n → ℝ)
    (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) :
    EssentiallySelfAdjointOn (nestedCore E) (fockSmoothPotentialOp W hW) := by sorry
