-- Prove2me | Theorems.Thm_BookProof_CoreBounds_norm_coreExt_le_inc
-- name    : BookProof.CoreBounds.norm_coreExt_le_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:16:33.92167+00:00
-- url     : https://prove2.me/theorems/8b68d6b5-80e6-4bdb-b55d-4f62f79d485a
-- title:
--   `BookProof.CoreBounds.norm_coreExt_le_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (x : maxDom c) : ‖coreExt hA...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.norm_coreExt_le_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ} (hA : CoreRelBound c H₀ A) (x : maxDom c) : ‖coreExt hA x‖ ≤ A * ‖(diagMax c x : L2I ι)‖
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.norm_coreExt_le_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_norm_coreExt_le`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.norm_coreExt_le_inc
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

theorem BookProof.CoreBounds.norm_coreExt_le_inc [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) (x : maxDom c) :
    ‖coreExt hA x‖ ≤ A * ‖(diagMax c x : L2I ι)‖ := by sorry
