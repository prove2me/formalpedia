-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilFun_embFun
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:37.830153+00:00
-- url     : https://prove2.me/theorems/b0074f94-7b02-4ec1-a070-ae8a0a6a4324
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun` (κ : J → ℝ) (j : J) (a : ℕ → ℂ) : bilFun κ (embFun j a) = embFun j (hFun (κ j) a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun` (κ : J → ℝ) (j : J) (a : ℕ → ℂ) : bilFun κ (embFun j a) = embFun j (hFun (κ j) a)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun (κ : J → ℝ) (j : J) (a : ℕ → ℂ) :
    bilFun κ (embFun j a) = embFun j (hFun (κ j) a) := by sorry
