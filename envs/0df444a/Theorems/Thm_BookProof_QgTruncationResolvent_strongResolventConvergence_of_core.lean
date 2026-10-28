-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_strongResolventConvergence_of_core
-- name    : BookProof.QgTruncationResolvent.strongResolventConvergence_of_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:37:36.783599+00:00
-- url     : https://prove2.me/theorems/cd1b86f1-850c-4d98-9ae3-8ff4349e8bfa
-- title:
--   `BookProof.QgTruncationResolvent.strongResolventConvergence_of_core` {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F} {Hn : ℕ → (D →ₗ[ℂ] F)} {T : UnboundedSelfAdjoint F} {S : ℕ →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.strongResolventConvergence_of_core` {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F} {Hn : ℕ → (D →ₗ[ℂ] F)} {T : UnboundedSelfAdjoint F} {S : ℕ → UnboundedSelfAdjoint F} (hesa : EssentiallySelfAdjointOn D Hc) (hT : IsSelfAdjointExtension Hc T.op) (hS : ∀ n, IsSelfAdjointExtension (Hn n) (S n).op) (hconv : ∀ x : D, Tendsto (fun n => Hn n x) atTop (𝓝 (Hc x))) : StrongResolventConvergence T S
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.strongResolventConvergence_of_core`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.strongResolventConvergence_of_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgTruncationResolvent.strongResolventConvergence_of_core {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {Hn : ℕ → (D →ₗ[ℂ] F)} {T : UnboundedSelfAdjoint F} {S : ℕ → UnboundedSelfAdjoint F}
    (hesa : EssentiallySelfAdjointOn D Hc) (hT : IsSelfAdjointExtension Hc T.op)
    (hS : ∀ n, IsSelfAdjointExtension (Hn n) (S n).op)
    (hconv : ∀ x : D, Tendsto (fun n => Hn n x) atTop (𝓝 (Hc x))) :
    StrongResolventConvergence T S := by sorry
