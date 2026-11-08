-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_sBd_multiplicity
-- name    : BookProof.CarlemanSimplex.sBd_multiplicity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:48:36.985863+00:00
-- url     : https://prove2.me/theorems/7575e503-40d5-4067-94e1-a014a85c7924
-- title:
--   `BookProof.CarlemanSimplex.sBd_multiplicity` (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card) ≤ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.sBd_multiplicity` (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card) ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.sBd_multiplicity`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.sBd_multiplicity
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

theorem BookProof.CarlemanSimplex.sBd_multiplicity (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card) ≤ k := by sorry
