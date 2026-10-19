-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_unifDist_mem_simplex
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:42.010893+00:00
-- url     : https://prove2.me/theorems/e3e89428-437f-4263-b0ad-bfad5debf253
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : unifDist n k ∈ stdSimplex ℝ (Fin n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex` {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : unifDist n k ∈ stdSimplex ℝ (Fin n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
open BookProof.ChapterFreeFieldBornFiberSpectrum


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    unifDist n k ∈ stdSimplex ℝ (Fin n) := by sorry
