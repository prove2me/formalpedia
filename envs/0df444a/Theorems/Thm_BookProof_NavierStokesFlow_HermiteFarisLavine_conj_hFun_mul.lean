-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_conj_hFun_mul
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:21.659982+00:00
-- url     : https://prove2.me/theorems/194fdfb3-6fcc-4b17-89d7-4ae9bfef241e
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul` (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) : (starRingEnd ℂ) (hFun κ X m) * Y m = -Complex.I * shift2 (crossA κ X Y) m + Complex.I
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul` (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) : (starRingEnd ℂ) (hFun κ X m) * Y m = -Complex.I * shift2 (crossA κ X Y) m + Complex.I * crossB κ X Y m
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.conj_hFun_mul (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) :
    (starRingEnd ℂ) (hFun κ X m) * Y m
      = -Complex.I * shift2 (crossA κ X Y) m + Complex.I * crossB κ X Y m := by sorry
