-- Prove2me | Theorems.Thm_BookProof_ChapterIPin_ipin_right
-- name    : BookProof.ChapterIPin.ipin_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:25.127565+00:00
-- url     : https://prove2.me/theorems/73a5cfeb-0105-4385-b99b-4eb3eed9b730
-- title:
--   `BookProof.ChapterIPin.ipin_right` (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) : (x * y).right = x.right * y.right
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIPin`.
--
--   `BookProof.ChapterIPin.ipin_right` (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) : (x * y).right = x.right * y.right
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIPin.ipin_right`.

-- Generated from ChapterIPin.lean — theorem BookProof.ChapterIPin.ipin_right
import Mathlib
import Definitions.Def_ChapterIPin
open BookProof.ChapterIPin



open Multiplicative

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

theorem BookProof.ChapterIPin.ipin_right (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) :
    (x * y).right = x.right * y.right := by sorry
