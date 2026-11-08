-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_mem_obd
-- name    : BookProof.CarlemanGeneralHop.mem_obd
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:42:42.896794+00:00
-- url     : https://prove2.me/theorems/7ffc93a5-bd5b-40cb-9ef5-f27ba983a90a
-- title:
--   `BookProof.CarlemanGeneralHop.mem_obd` {N : ℕ} {p m a : Fin d →₀ ℕ} : a ∈ obd d N p m ↔ (∀ k, a k ≤ N) ∧ (∀ k, m k ≤ a k) ∧ ∃ k, N < a k + p k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.mem_obd` {N : ℕ} {p m a : Fin d →₀ ℕ} : a ∈ obd d N p m ↔ (∀ k, a k ≤ N) ∧ (∀ k, m k ≤ a k) ∧ ∃ k, N < a k + p k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.mem_obd`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.mem_obd
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

theorem BookProof.CarlemanGeneralHop.mem_obd {N : ℕ} {p m a : Fin d →₀ ℕ} :
    a ∈ obd d N p m ↔ (∀ k, a k ≤ N) ∧ (∀ k, m k ≤ a k) ∧ ∃ k, N < a k + p k := by sorry
