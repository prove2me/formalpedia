-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_sum
-- name    : BookProof.NavierStokesFlow.Carleman.tridiagOp_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:36:48.572412+00:00
-- url     : https://prove2.me/theorems/ad94a828-1f02-42e1-b338-d9bd520b8db8
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_sum` {ι : Type*} (s : Finset ι) (cc : ι → ℕ → ℂ) : (∑ i ∈ s, tridiagOp (cc i)) = tridiagOp (fun n => ∑ i ∈ s, cc i n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_sum` {ι : Type*} (s : Finset ι) (cc : ι → ℕ → ℂ) : (∑ i ∈ s, tridiagOp (cc i)) = tridiagOp (fun n => ∑ i ∈ s, cc i n)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiagOp_sum`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_sum {ι : Type*} (s : Finset ι) (cc : ι → ℕ → ℂ) :
    (∑ i ∈ s, tridiagOp (cc i)) = tridiagOp (fun n => ∑ i ∈ s, cc i n) := by sorry
