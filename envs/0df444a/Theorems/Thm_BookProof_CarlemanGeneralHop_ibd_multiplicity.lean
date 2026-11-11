-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_multiplicity
-- name    : BookProof.CarlemanGeneralHop.ibd_multiplicity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:00.725206+00:00
-- url     : https://prove2.me/theorems/619914ff-562d-4377-b7d7-2f3f405d6f1d
-- title:
--   `BookProof.CarlemanGeneralHop.ibd_multiplicity` (m : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ ibd d N m)).card) ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ibd_multiplicity` (m : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => b ∈ ibd d N m)).card) ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ibd_multiplicity`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ibd_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
open BookProof.CarlemanGeneralHop



open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanGeneralHop.ibd_multiplicity (m : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => b ∈ ibd d N m)).card) ≤ 1 := by sorry
