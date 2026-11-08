-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_le
-- name    : BookProof.CarlemanGeneralHop.hshift_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:41:58.738933+00:00
-- url     : https://prove2.me/theorems/fdbc659a-83c6-4426-a8ba-bf7fe326a136
-- title:
--   `BookProof.CarlemanGeneralHop.hshift_le` {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) (k : Fin d) : p k ≤ hshift p m a k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.hshift_le` {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) (k : Fin d) : p k ≤ hshift p m a k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.hshift_le`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.hshift_le
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

theorem BookProof.CarlemanGeneralHop.hshift_le {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) (k : Fin d) :
    p k ≤ hshift p m a k := by sorry
