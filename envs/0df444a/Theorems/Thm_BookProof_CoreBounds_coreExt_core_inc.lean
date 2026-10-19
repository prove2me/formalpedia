-- Prove2me | Theorems.Thm_BookProof_CoreBounds_coreExt_core_inc
-- name    : BookProof.CoreBounds.coreExt_core_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:16:34.745396+00:00
-- url     : https://prove2.me/theorems/57d20992-2e28-42db-9b38-44f8f4158ae1
-- title:
--   `BookProof.CoreBounds.coreExt_core_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (u : lpFiniteModes ι) : coreExtFun c...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.coreExt_core_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (u : lpFiniteModes ι) : coreExtFun c H₀ (inclC c u) = H₀ u
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.coreExt_core_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_coreExt_core`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.coreExt_core_inc
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
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

theorem BookProof.CoreBounds.coreExt_core_inc [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) (u : lpFiniteModes ι) :
    coreExtFun c H₀ (inclC c u) = H₀ u := by sorry
