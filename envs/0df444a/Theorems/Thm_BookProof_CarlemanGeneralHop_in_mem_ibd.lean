-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_in_mem_ibd
-- name    : BookProof.CarlemanGeneralHop.in_mem_ibd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:43:21.200514+00:00
-- url     : https://prove2.me/theorems/db31a5b9-005c-41d8-a295-b9f1d9fa8ee6
-- title:
--   `BookProof.CarlemanGeneralHop.in_mem_ibd` {N : ℕ} {p m : Fin d →₀ ℕ} (hm1 : ∀ k, m k ≤ 1) {b : Fin d →₀ ℕ} (hb : b ∈ hopB (cube d N) p m \ cube d N) : b ∈ ibd d N m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.in_mem_ibd` {N : ℕ} {p m : Fin d →₀ ℕ} (hm1 : ∀ k, m k ≤ 1) {b : Fin d →₀ ℕ} (hb : b ∈ hopB (cube d N) p m \ cube d N) : b ∈ ibd d N m
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.in_mem_ibd`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.in_mem_ibd
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

theorem BookProof.CarlemanGeneralHop.in_mem_ibd {N : ℕ} {p m : Fin d →₀ ℕ} (hm1 : ∀ k, m k ≤ 1) {b : Fin d →₀ ℕ}
    (hb : b ∈ hopB (cube d N) p m \ cube d N) : b ∈ ibd d N m := by sorry
