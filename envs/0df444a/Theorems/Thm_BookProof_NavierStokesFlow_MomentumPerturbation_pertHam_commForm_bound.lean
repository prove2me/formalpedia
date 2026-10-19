-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_commForm_bound
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:19.492133+00:00
-- url     : https://prove2.me/theorems/5e61e26f-b319-4e1c-832c-1ec32a48901f
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound` (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c) (x : maxDom c) : |commForm (pertHam c (u : L2I ι) (w : L2I
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound` (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c) (x : maxDom c) : |commForm (pertHam c (u : L2I ι) (w : L2I ι)) (diagMax c) x| ≤ (2 * (‖(u : L2I ι)‖ * ‖diagMax c w‖ + ‖(w : L2I ι)‖ * ‖diagMax c u‖)) * quadForm (diagMax c) x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_commForm_bound (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c)
    (x : maxDom c) :
    |commForm (pertHam c (u : L2I ι) (w : L2I ι)) (diagMax c) x|
      ≤ (2 * (‖(u : L2I ι)‖ * ‖diagMax c w‖ + ‖(w : L2I ι)‖ * ‖diagMax c u‖))
        * quadForm (diagMax c) x := by sorry
