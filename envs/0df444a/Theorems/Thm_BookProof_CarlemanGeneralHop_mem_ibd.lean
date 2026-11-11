-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_mem_ibd
-- name    : BookProof.CarlemanGeneralHop.mem_ibd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:42:26.861813+00:00
-- url     : https://prove2.me/theorems/80dcd8fb-07d2-4d55-8bec-0d94aaae8f21
-- title:
--   `BookProof.CarlemanGeneralHop.mem_ibd` {N : ℕ} {m b : Fin d →₀ ℕ} : b ∈ ibd d N m ↔ (∀ k, b k ≤ N + 1) ∧ (∀ k, m k ≤ b k) ∧ ¬ (∀ k, b k ≤ N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.mem_ibd` {N : ℕ} {m b : Fin d →₀ ℕ} : b ∈ ibd d N m ↔ (∀ k, b k ≤ N + 1) ∧ (∀ k, m k ≤ b k) ∧ ¬ (∀ k, b k ≤ N)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.mem_ibd`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.mem_ibd
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

theorem BookProof.CarlemanGeneralHop.mem_ibd {N : ℕ} {m b : Fin d →₀ ℕ} :
    b ∈ ibd d N m ↔ (∀ k, b k ≤ N + 1) ∧ (∀ k, m k ≤ b k) ∧ ¬ (∀ k, b k ≤ N) := by sorry
