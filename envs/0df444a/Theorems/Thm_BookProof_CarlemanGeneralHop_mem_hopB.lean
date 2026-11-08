-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_mem_hopB
-- name    : BookProof.CarlemanGeneralHop.mem_hopB
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:42:13.743343+00:00
-- url     : https://prove2.me/theorems/97c8b521-0c3e-4318-817d-9141b36b7725
-- title:
--   `BookProof.CarlemanGeneralHop.mem_hopB` {A : Finset (Fin d →₀ ℕ)} {p m b : Fin d →₀ ℕ} : b ∈ hopB A p m ↔ (∀ k, m k ≤ b k) ∧ hshift p m b ∈ A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.mem_hopB` {A : Finset (Fin d →₀ ℕ)} {p m b : Fin d →₀ ℕ} : b ∈ hopB A p m ↔ (∀ k, m k ≤ b k) ∧ hshift p m b ∈ A
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.mem_hopB`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.mem_hopB
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

theorem BookProof.CarlemanGeneralHop.mem_hopB {A : Finset (Fin d →₀ ℕ)} {p m b : Fin d →₀ ℕ} :
    b ∈ hopB A p m ↔ (∀ k, m k ≤ b k) ∧ hshift p m b ∈ A := by sorry
