-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_bogoliubov_essentiallySelfAdjointOn_core
-- name    : BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-13T05:02:00.788327+00:00
-- url     : https://prove2.me/theorems/d1f25276-1478-4bfc-8d01-0e0e53268862
-- title:
--   `BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core` (hω : ∀ i, 0 ≤ ω i) (m n : κ → ι) (g : κ → ℂ) (hsum : Summable fun k => ‖g k‖ * (ω (m k) + ω (n k) + 2)) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core` (hω : ∀ i, 0 ≤ ω i) (m n : κ → ι) (g : κ → ℂ) (hsum : Summable fun k => ‖g k‖ * (ω (m k) + ω (n k) + 2)) : EssentiallySelfAdjointOn (lpFiniteModes (Idx ι)) ((fockH hω (fun k => pairIdx (m k) (n k)) (fun _ => (0 : Idx ι)) g (fun k => by simp) (by refine hsum.congr fun k => ?_ simp [wsum_pairIdx])).comp (Submodule.inclusion (finiteModes_le_maxDom (sig ω))))
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_FockQuadratic_wsum_pairIdx
open BookProof.ChapterA3n
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockQuadratic


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ω : ι → ℝ}
variable {κ : Type*}

theorem BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (m n : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖ * (ω (m k) + ω (n k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω (fun k => pairIdx (m k) (n k)) (fun _ => (0 : Idx ι)) g
          (fun k => by simp)
          (by
            refine hsum.congr fun k => ?_
            simp [wsum_pairIdx])).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := by sorry
