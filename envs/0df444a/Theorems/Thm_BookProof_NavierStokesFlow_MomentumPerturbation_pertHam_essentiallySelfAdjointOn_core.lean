-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:19.268013+00:00
-- url     : https://prove2.me/theorems/9fefb5bc-f10c-4b7f-91a7-aca40a80b9a2
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core` (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c) : EssentiallySelfAdjointOn (lpFiniteModes ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core` (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c) : EssentiallySelfAdjointOn (lpFiniteModes ι) ((pertHam c (u : L2I ι) (w : L2I ι)).comp (Submodule.inclusion (finiteModes_le_maxDom c)))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k)
    (u w : maxDom c) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((pertHam c (u : L2I ι) (w : L2I ι)).comp
        (Submodule.inclusion (finiteModes_le_maxDom c))) := by sorry
