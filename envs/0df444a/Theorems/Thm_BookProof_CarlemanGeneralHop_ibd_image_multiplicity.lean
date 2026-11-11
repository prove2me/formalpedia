-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_image_multiplicity
-- name    : BookProof.CarlemanGeneralHop.ibd_image_multiplicity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:16.270964+00:00
-- url     : https://prove2.me/theorems/5bd6deeb-c7fb-452e-b291-0588ab8434f9
-- title:
--   `BookProof.CarlemanGeneralHop.ibd_image_multiplicity` (p m : Fin d →₀ ℕ) (y : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => y ∈ (ibd d N m).image (hshift p m))).card) ≤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ibd_image_multiplicity` (p m : Fin d →₀ ℕ) (y : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => y ∈ (ibd d N m).image (hshift p m))).card) ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ibd_image_multiplicity`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ibd_image_multiplicity
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

theorem BookProof.CarlemanGeneralHop.ibd_image_multiplicity (p m : Fin d →₀ ℕ) (y : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => y ∈ (ibd d N m).image (hshift p m))).card) ≤ 1 := by sorry
