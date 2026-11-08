-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_obd_shift_mass_le
-- name    : BookProof.CarlemanGeneralHop.obd_shift_mass_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:43:49.93559+00:00
-- url     : https://prove2.me/theorems/3eae89ff-5692-45e1-8dec-39fbaae06dc4
-- title:
--   `BookProof.CarlemanGeneralHop.obd_shift_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (M : ℕ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.obd_shift_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ obd d N p m, ‖u (hshift p m a)‖ ^ 2 ≤ 2 * B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.obd_shift_mass_le`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.obd_shift_mass_le
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

theorem BookProof.CarlemanGeneralHop.obd_shift_mass_le {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ obd d N p m, ‖u (hshift p m a)‖ ^ 2 ≤ 2 * B := by sorry
