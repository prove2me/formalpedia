-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_amp_eq_zero_of_not_mem_obd
-- name    : BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:42:48.585991+00:00
-- url     : https://prove2.me/theorems/a08de214-86d6-4817-a7af-309430faba33
-- title:
--   `BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd` {N : ℕ} {p m : Fin d →₀ ℕ} {c : (Fin d →₀ ℕ) → ℝ} (hvanR : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, m k ≤ a k) → c a =...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd` {N : ℕ} {p m : Fin d →₀ ℕ} {c : (Fin d →₀ ℕ) → ℝ} (hvanR : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, m k ≤ a k) → c a = 0) {a : Fin d →₀ ℕ} (ha : a ∈ cube d N \ hopB (cube d N) p m) (hne : a ∉ obd d N p m) : c a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanGeneralHop



open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd {N : ℕ} {p m : Fin d →₀ ℕ} {c : (Fin d →₀ ℕ) → ℝ}
    (hvanR : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, m k ≤ a k) → c a = 0) {a : Fin d →₀ ℕ}
    (ha : a ∈ cube d N \ hopB (cube d N) p m) (hne : a ∉ obd d N p m) : c a = 0 := by sorry
