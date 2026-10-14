-- Prove2me | Theorems.Thm_BookProof_ScalaronFock_qgScalaronModeFock_stone_flow
-- name    : BookProof.ScalaronFock.qgScalaronModeFock_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:54.914545+00:00
-- url     : https://prove2.me/theorems/4ce71913-3e3b-478d-b504-847512e76219
-- title:
--   `BookProof.ScalaronFock.qgScalaronModeFock_stone_flow` : ∃ (T : UnboundedSelfAdjoint modeFock) (U : ℝ → (modeFock →L[ℂ] modeFock)), IsSelfAdjointExtension (qgScalaronModeFockHamilt
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronFockEsa`.
--
--   `BookProof.ScalaronFock.qgScalaronModeFock_stone_flow` : ∃ (T : UnboundedSelfAdjoint modeFock) (U : ℝ → (modeFock →L[ℂ] modeFock)), IsSelfAdjointExtension (qgScalaronModeFockHamiltonian a b M alpha Rc phi) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronFock.qgScalaronModeFock_stone_flow`.

-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronModeFock_stone_flow
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.FarisLavine
open BookProof.StoneBridge
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
variable (a b : ℕ → ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℕ → ℝ)

theorem BookProof.ScalaronFock.qgScalaronModeFock_stone_flow :
    ∃ (T : UnboundedSelfAdjoint modeFock) (U : ℝ → (modeFock →L[ℂ] modeFock)),
      IsSelfAdjointExtension (qgScalaronModeFockHamiltonian a b M alpha Rc phi) T.op ∧
        IsStoneFlow T U := by sorry
