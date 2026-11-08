-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
-- name    : BookProof.CarlemanGeneralHop.hshift_hshift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:41:38.541661+00:00
-- url     : https://prove2.me/theorems/4d994739-c77a-41ea-93dd-e4559890e372
-- title:
--   `BookProof.CarlemanGeneralHop.hshift_hshift` {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) : hshift m p (hshift p m a) = a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.hshift_hshift` {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) : hshift m p (hshift p m a) = a
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.hshift_hshift`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.hshift_hshift
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

theorem BookProof.CarlemanGeneralHop.hshift_hshift {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) :
    hshift m p (hshift p m a) = a := by sorry
