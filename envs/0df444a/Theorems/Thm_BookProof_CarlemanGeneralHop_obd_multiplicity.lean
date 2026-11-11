-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_obd_multiplicity
-- name    : BookProof.CarlemanGeneralHop.obd_multiplicity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:42:58.147684+00:00
-- url     : https://prove2.me/theorems/898ceb5c-6cbd-480c-96c1-5860344a5c38
-- title:
--   `BookProof.CarlemanGeneralHop.obd_multiplicity` (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ obd d N p m)).card) ≤ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.obd_multiplicity` (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (a : Fin d →₀ ℕ) (M : ℕ) : (((Finset.range M).filter (fun N => a ∈ obd d N p m)).card) ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.obd_multiplicity`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.obd_multiplicity
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

theorem BookProof.CarlemanGeneralHop.obd_multiplicity (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ obd d N p m)).card) ≤ 2 := by sorry
