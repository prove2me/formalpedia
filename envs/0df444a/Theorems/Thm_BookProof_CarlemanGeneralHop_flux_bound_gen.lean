-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_flux_bound_gen
-- name    : BookProof.CarlemanGeneralHop.flux_bound_gen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:43:37.81541+00:00
-- url     : https://prove2.me/theorems/c48282f8-a16d-4475-a30e-73db7df68504
-- title:
--   `BookProof.CarlemanGeneralHop.flux_bound_gen` {w : ℂ} {c : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ} (F G : Finset (Fin d →₀ ℕ)) (hzero : ∀ a ∈ F, a ∉ G → c a = 0) {Cn...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.flux_bound_gen` {w : ℂ} {c : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ} (F G : Finset (Fin d →₀ ℕ)) (hzero : ∀ a ∈ F, a ∉ G → c a = 0) {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ G, |c a| ≤ Cn) : |(∑ a ∈ F, rtG u w c p m a).im| ≤ Cn * (‖w‖ * ((∑ a ∈ G, (‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2)) / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.flux_bound_gen`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.flux_bound_gen
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

theorem BookProof.CarlemanGeneralHop.flux_bound_gen {w : ℂ} {c : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ}
    (F G : Finset (Fin d →₀ ℕ)) (hzero : ∀ a ∈ F, a ∉ G → c a = 0)
    {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ G, |c a| ≤ Cn) :
    |(∑ a ∈ F, rtG u w c p m a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ G, (‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2)) / 2)) := by sorry
