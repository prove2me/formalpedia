-- Prove2me | Theorems.Thm_BookProof_CoreBounds_tendsto_trunc_inc
-- name    : BookProof.CoreBounds.tendsto_trunc_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:16:36.095583+00:00
-- url     : https://prove2.me/theorems/32b5d28c-562f-45fe-97fe-8f4ac9027e96
-- title:
--   `BookProof.CoreBounds.tendsto_trunc_inc` [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) : Tendsto (fun S : Finset ι => ((trunc c x S : lpFiniteModes ι) : L2I ι)) atTop (𝓝 ((x : L2I ι)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoreBoundsEsa`.
--
--   `BookProof.CoreBounds.tendsto_trunc_inc` [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) : Tendsto (fun S : Finset ι => ((trunc c x S : lpFiniteModes ι) : L2I ι)) atTop (𝓝 ((x : L2I ι)))
--
--   Formalization note: Lean 4 identifier `BookProof.CoreBounds.tendsto_trunc_inc`.
--
--   Replaces the unuploadable node `BookProof_CoreBounds_tendsto_trunc`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterCoreBoundsEsa.lean — theorem BookProof.CoreBounds.tendsto_trunc_inc
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

theorem BookProof.CoreBounds.tendsto_trunc_inc [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) :
    Tendsto (fun S : Finset ι => ((trunc c x S : lpFiniteModes ι) : L2I ι)) atTop
      (𝓝 ((x : L2I ι))) := by sorry
