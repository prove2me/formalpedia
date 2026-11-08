-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_shift_mass_le
-- name    : BookProof.CarlemanGeneralHop.ibd_shift_mass_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:09.975199+00:00
-- url     : https://prove2.me/theorems/99fa517e-1130-4c54-8bff-0d9791392a2e
-- title:
--   `BookProof.CarlemanGeneralHop.ibd_shift_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (p m : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ibd_shift_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (p m : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ b ∈ ibd d N m, ‖u (hshift p m b)‖ ^ 2 ≤ B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ibd_shift_mass_le`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ibd_shift_mass_le
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

theorem BookProof.CarlemanGeneralHop.ibd_shift_mass_le {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (p m : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ b ∈ ibd d N m, ‖u (hshift p m b)‖ ^ 2 ≤ B := by sorry
