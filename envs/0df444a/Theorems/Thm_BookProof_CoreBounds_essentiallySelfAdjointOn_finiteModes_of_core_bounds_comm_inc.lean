-- Prove2me | Theorems.Thm_BookProof_CoreBounds_essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
-- name    : BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:17:42.388641+00:00
-- url     : https://prove2.me/theorems/50ff35e9-3654-4147-94dc-a3fce08dc493
-- title:
--   `BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc` (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ) (hsym : ∀ u v...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc` (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ) (hsym : ∀ u v : lpFiniteModes ι, (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v)) (hA : CoreRelBound c H₀ A) (hcomm : ∀ u : lpFiniteModes ι, (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im = 0) : EssentiallySelfAdjointOn (lpFiniteModes ι) H₀
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
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

theorem BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v))
    (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im = 0) :
    EssentiallySelfAdjointOn (lpFiniteModes ι) H₀ := by sorry
