-- Prove2me | Theorems.Thm_BookProof_FockDegreesOfFreedom_card_ghost_eq_two_mul
-- name    : BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:20:06.710784+00:00
-- url     : https://prove2.me/theorems/eed5de27-2d54-435e-8168-0199b10f65a4
-- title:
--   `BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul` (k : ℕ) : Fintype.card (Fin (k + 1) → ZMod 2) = 2 * Fintype.card (Fin k → ZMod 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDegreesOfFreedom`.
--
--   `BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul` (k : ℕ) : Fintype.card (Fin (k + 1) → ZMod 2) = 2 * Fintype.card (Fin k → ZMod 2)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul`.

-- Generated from ChapterFockDegreesOfFreedom.lean — theorem BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom



open Fintype

theorem BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul (k : ℕ) :
    Fintype.card (Fin (k + 1) → ZMod 2) = 2 * Fintype.card (Fin k → ZMod 2) := by sorry
