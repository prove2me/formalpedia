-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:19.672231+00:00
-- url     : https://prove2.me/theorems/813e50c6-4d29-4932-b54e-51b6d79e4a56
-- title:
--   `BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (hcar : ¬ Summable fun n => 1 / ‖nsCoupling (halfLineSymbol c nu) n‖) : HasZero
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (hcar : ¬ Summable fun n => 1 / ‖nsCoupling (halfLineSymbol c nu) n‖) : HasZeroDeficiencyOn (halfLineFullData c nu).D (halfLineFullData c nu).hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn (c : Fin 15 → ℕ → ℝ) (nu : ℝ)
    (hcar : ¬ Summable fun n => 1 / ‖nsCoupling (halfLineSymbol c nu) n‖) :
    HasZeroDeficiencyOn (halfLineFullData c nu).D (halfLineFullData c nu).hamiltonian := by sorry
