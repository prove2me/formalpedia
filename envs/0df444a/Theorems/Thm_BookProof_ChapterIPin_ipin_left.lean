-- Prove2me | Theorems.Thm_BookProof_ChapterIPin_ipin_left
-- name    : BookProof.ChapterIPin.ipin_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:58.095861+00:00
-- url     : https://prove2.me/theorems/bb6a0168-8909-48b2-aea3-d4fe8beb885e
-- title:
--   `BookProof.ChapterIPin.ipin_left` (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) : toAdd (x * y).left = toAdd x.left + Multiplicative.toAdd (Λ x.right) (toAdd y.left)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIPin`.
--
--   `BookProof.ChapterIPin.ipin_left` (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) : toAdd (x * y).left = toAdd x.left + Multiplicative.toAdd (Λ x.right) (toAdd y.left)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterIPin.ipin_left`.

-- Generated from ChapterIPin.lean — theorem BookProof.ChapterIPin.ipin_left
import Mathlib
import Definitions.Def_ChapterIPin
open BookProof.ChapterIPin



open Multiplicative

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

theorem BookProof.ChapterIPin.ipin_left (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) :
    toAdd (x * y).left = toAdd x.left + Multiplicative.toAdd (Λ x.right) (toAdd y.left) := by sorry
