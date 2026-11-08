-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_obd_image_multiplicity
-- name    : BookProof.CarlemanGeneralHop.obd_image_multiplicity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:43:09.493981+00:00
-- url     : https://prove2.me/theorems/21aab4c5-a8ac-42a0-be92-7d666d3c8eec
-- title:
--   `BookProof.CarlemanGeneralHop.obd_image_multiplicity` (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (y : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => y ∈ (obd d N p m).image
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.obd_image_multiplicity` (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (y : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => y ∈ (obd d N p m).image (hshift p m))).card) ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.obd_image_multiplicity`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.obd_image_multiplicity
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

theorem BookProof.CarlemanGeneralHop.obd_image_multiplicity (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (y : Fin d →₀ ℕ)
    (M : ℕ) :
    (((Finset.range M).filter
      (fun N => y ∈ (obd d N p m).image (hshift p m))).card) ≤ 2 := by sorry
