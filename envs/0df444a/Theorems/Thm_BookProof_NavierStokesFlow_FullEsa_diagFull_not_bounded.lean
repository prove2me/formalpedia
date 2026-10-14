-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagFull_not_bounded
-- name    : BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:39.454971+00:00
-- url     : https://prove2.me/theorems/ba653d72-f923-4a4c-823d-20bbe1dc41cb
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded` : ¬ ∃ C : ℝ, ∀ f : diagUnboundedData.D, ‖diagUnboundedData.hamiltonian f‖ ≤ C * ‖f‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded` : ¬ ∃ C : ℝ, ∀ f : diagUnboundedData.D, ‖diagUnboundedData.hamiltonian f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.diagFull_not_bounded :
    ¬ ∃ C : ℝ, ∀ f : diagUnboundedData.D, ‖diagUnboundedData.hamiltonian f‖ ≤ C * ‖f‖ := by sorry
