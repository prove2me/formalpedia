-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiag_recursion_of_deficiency
-- name    : BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:36:05.742776+00:00
-- url     : https://prove2.me/theorems/3928fded-93a3-40f1-848e-f6b2c7b63e30
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency` (c : ℕ → ℂ) (z : ℂ) (w : L2N) (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ ((tridiagOp c v : lpFiniteModes ℕ) : L2N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency` (c : ℕ → ℂ) (z : ℂ) (w : L2N) (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ ((tridiagOp c v : lpFiniteModes ℕ) : L2N) w : ℂ) = inner ℂ ((v : lpFiniteModes ℕ) : L2N) (z • w)) : ∀ n, tridiagFun c ((w : L2N) : ℕ → ℂ) n = z * ((w : L2N) : ℕ → ℂ) n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency (c : ℕ → ℂ) (z : ℂ) (w : L2N)
    (hw : ∀ v : lpFiniteModes ℕ,
      (inner ℂ ((tridiagOp c v : lpFiniteModes ℕ) : L2N) w : ℂ)
        = inner ℂ ((v : lpFiniteModes ℕ) : L2N) (z • w)) :
    ∀ n, tridiagFun c ((w : L2N) : ℕ → ℂ) n = z * ((w : L2N) : ℕ → ℂ) n := by sorry
