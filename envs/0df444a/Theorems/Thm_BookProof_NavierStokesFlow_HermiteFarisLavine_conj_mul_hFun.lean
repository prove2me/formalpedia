-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_conj_mul_hFun
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:59.020975+00:00
-- url     : https://prove2.me/theorems/a80b67ad-2fe5-44ff-be90-5ea1a54d92de
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun` (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) : (starRingEnd ℂ) (X m) * hFun κ Y m = -Complex.I * crossA κ X Y m + Complex.I * shift2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun` (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) : (starRingEnd ℂ) (X m) * hFun κ Y m = -Complex.I * crossA κ X Y m + Complex.I * shift2 (crossB κ X Y) m
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.conj_mul_hFun (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) :
    (starRingEnd ℂ) (X m) * hFun κ Y m
      = -Complex.I * crossA κ X Y m + Complex.I * shift2 (crossB κ X Y) m := by sorry
