-- Prove2me | Theorems.Thm_BookProof_LorentzOrthochronous_product_time_component
-- name    : BookProof.LorentzOrthochronous.product_time_component
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:36:57.026091+00:00
-- url     : https://prove2.me/theorems/653e7202-7423-4194-8cbc-25a2f19a418b
-- title:
--   `BookProof.LorentzOrthochronous.product_time_component` (a b : Matrix (Fin 4) (Fin 4) ℝ) : (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 + a 0 2 * b 2 0 + a 0 3 * b 3 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzOrthochronous`.
--
--   `BookProof.LorentzOrthochronous.product_time_component` (a b : Matrix (Fin 4) (Fin 4) ℝ) : (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 + a 0 2 * b 2 0 + a 0 3 * b 3 0
--
--   Formalization note: Lean 4 identifier `BookProof.LorentzOrthochronous.product_time_component`.

-- Generated from ChapterLorentzOrthochronous.lean — theorem BookProof.LorentzOrthochronous.product_time_component
import Definitions.Def_ChapterLorentzGroup
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
open BookProof.LorentzOrthochronous



open Matrix
open BookProof.LorentzGroup

theorem BookProof.LorentzOrthochronous.product_time_component (a b : Matrix (Fin 4) (Fin 4) ℝ) :
    (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 + a 0 2 * b 2 0 + a 0 3 * b 3 0 := by sorry
