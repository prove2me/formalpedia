-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_embFun_of_ne
-- name    : BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:27.614141+00:00
-- url     : https://prove2.me/theorems/e5880a23-e9ef-4a33-a241-cda18a58a4d2
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne` {j j' : J} (a : ℕ → ℂ) (n : ℕ) (h : j' ≠ j) : embFun j a (n, j') = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne` {j j' : J} (a : ℕ → ℂ) (n : ℕ) (h : j' ≠ j) : embFun j a (n, j') = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.embFun_of_ne {j j' : J} (a : ℕ → ℂ) (n : ℕ) (h : j' ≠ j) : embFun j a (n, j') = 0 := by sorry
