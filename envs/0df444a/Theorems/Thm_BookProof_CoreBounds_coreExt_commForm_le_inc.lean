-- Prove2me | Theorems.Thm_BookProof_CoreBounds_coreExt_commForm_le_inc
-- name    : BookProof.CoreBounds.coreExt_commForm_le_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:16:43.291598+00:00
-- url     : https://prove2.me/theorems/cc7f0460-9a44-4ab6-bd99-45233f81f369
-- title:
--   `BookProof.CoreBounds.coreExt_commForm_le_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A B : ℝ} (hA : CoreRelBound c H₀ A) (hcomm : ∀ u :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.coreExt_commForm_le_inc` [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A B : ℝ} (hA : CoreRelBound c H₀ A) (hcomm : ∀ u : lpFiniteModes ι, |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im| ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re) (x : maxDom c) : |commForm (coreExt hA) (diagMax c) x| ≤ B * quadForm (diagMax c) x
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.coreExt_commForm_le_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_coreExt_commForm_le`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.coreExt_commForm_le_inc
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

theorem BookProof.CoreBounds.coreExt_commForm_le_inc [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A B : ℝ} (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im|
        ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re)
    (x : maxDom c) :
    |commForm (coreExt hA) (diagMax c) x| ≤ B * quadForm (diagMax c) x := by sorry
