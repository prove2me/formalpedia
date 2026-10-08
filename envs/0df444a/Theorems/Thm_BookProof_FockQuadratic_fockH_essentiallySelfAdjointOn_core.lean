-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_fockH_essentiallySelfAdjointOn_core
-- name    : BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T21:14:57.386409+00:00
-- url     : https://prove2.me/theorems/fcaec263-52c8-4209-bc30-e128b34418fd
-- title:
--   `BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core` (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ) (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core` (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ) (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2)) : EssentiallySelfAdjointOn (lpFiniteModes (Idx ι)) ((fockH hω P Q g hPQ hsum).comp (Submodule.inclusion (finiteModes_le_maxDom (sig ω))))
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core
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
open BookProof.ChapterA3n
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2)
    (hsum : Summable fun k => ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω P Q g hPQ hsum).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := by sorry
