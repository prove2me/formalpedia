-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_mass_le
-- name    : BookProof.CarlemanGeneralHop.ibd_mass_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:44:28.057536+00:00
-- url     : https://prove2.me/theorems/179f92a2-8887-4127-a5d5-68d90a59e752
-- title:
--   `BookProof.CarlemanGeneralHop.ibd_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (m : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range M, ∑...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ibd_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (m : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ b ∈ ibd d N m, ‖u b‖ ^ 2 ≤ B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ibd_mass_le`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ibd_mass_le
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

theorem BookProof.CarlemanGeneralHop.ibd_mass_le {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (m : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ b ∈ ibd d N m, ‖u b‖ ^ 2 ≤ B := by sorry
