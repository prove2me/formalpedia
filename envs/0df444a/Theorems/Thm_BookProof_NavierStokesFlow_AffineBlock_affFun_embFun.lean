-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_affFun_embFun
-- name    : BookProof.NavierStokesFlow.AffineBlock.affFun_embFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:42:33.985509+00:00
-- url     : https://prove2.me/theorems/c63f9d3a-b97e-48da-8946-0456b5bc2edf
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.affFun_embFun` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (j : J) (a : ℕ → ℂ) : affFun κ c hκ hc (embFun j a) = embFun j...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.affFun_embFun` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (j : J) (a : ℕ → ℂ) : affFun κ c hκ hc (embFun j a) = embFun j (fun n => (affData (hκ j) (hc j)).fst.hFun a n + (affData (hκ j) (hc j)).snd.hFun a n)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.affFun_embFun`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affFun_embFun
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

theorem BookProof.NavierStokesFlow.AffineBlock.affFun_embFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (j : J) (a : ℕ → ℂ) :
    affFun κ c hκ hc (embFun j a)
      = embFun j (fun n => (affData (hκ j) (hc j)).fst.hFun a n
          + (affData (hκ j) (hc j)).snd.hFun a n) := by sorry
