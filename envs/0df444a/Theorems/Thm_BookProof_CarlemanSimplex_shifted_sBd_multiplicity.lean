-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_shifted_sBd_multiplicity
-- name    : BookProof.CarlemanSimplex.shifted_sBd_multiplicity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:07.146549+00:00
-- url     : https://prove2.me/theorems/f5371fda-3d2b-46e5-a191-e99a98078e5a
-- title:
--   `BookProof.CarlemanSimplex.shifted_sBd_multiplicity` (P : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.shifted_sBd_multiplicity` (P : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card) ≤ deg P
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.shifted_sBd_multiplicity`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.shifted_sBd_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanSimplex.shifted_sBd_multiplicity (P : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card) ≤ deg P := by sorry
