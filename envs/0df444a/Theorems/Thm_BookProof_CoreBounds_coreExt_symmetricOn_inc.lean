-- Prove2me | Theorems.Thm_BookProof_CoreBounds_coreExt_symmetricOn_inc
-- name    : BookProof.CoreBounds.coreExt_symmetricOn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:16:54.737981+00:00
-- url     : https://prove2.me/theorems/89516243-4057-4abe-b098-ddfc521d4b0e
-- title:
--   `BookProof.CoreBounds.coreExt_symmetricOn_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (hsym : ∀ u v :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.coreExt_symmetricOn_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (hsym : ∀ u v : lpFiniteModes ι, (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v)) : SymmetricOn (maxDom c) (coreExt hA)
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.coreExt_symmetricOn_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_coreExt_symmetricOn`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.coreExt_symmetricOn_inc
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.CoreBounds



open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries
open Filter Topology

noncomputable section

variable {ι : Type*} {c : ι → ℝ}

variable (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)

theorem BookProof.CoreBounds.coreExt_symmetricOn_inc [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v)) :
    SymmetricOn (maxDom c) (coreExt hA) := by sorry
