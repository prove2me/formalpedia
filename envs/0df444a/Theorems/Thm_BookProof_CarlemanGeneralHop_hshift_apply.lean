-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_apply
-- name    : BookProof.CarlemanGeneralHop.hshift_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:41:28.08566+00:00
-- url     : https://prove2.me/theorems/94065bee-de2e-470d-a369-3666980868cc
-- title:
--   `BookProof.CarlemanGeneralHop.hshift_apply` (p m a : Fin d →₀ ℕ) (k : Fin d) : hshift p m a k = a k + p k - m k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.hshift_apply` (p m a : Fin d →₀ ℕ) (k : Fin d) : hshift p m a k = a k + p k - m k
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.hshift_apply`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.hshift_apply
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

theorem BookProof.CarlemanGeneralHop.hshift_apply (p m a : Fin d →₀ ℕ) (k : Fin d) :
    hshift p m a k = a k + p k - m k := by sorry
