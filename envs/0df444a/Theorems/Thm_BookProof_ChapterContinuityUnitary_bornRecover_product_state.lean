-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornRecover_product_state
-- name    : BookProof.ChapterContinuityUnitary.bornRecover_product_state
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:07:17.756875+00:00
-- url     : https://prove2.me/theorems/849a96c0-567f-4320-b7a1-e1a32b224068
-- title:
--   The Lean 4 theorem `bornRecover_product_state` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornRecover_product_state` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_product_state
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]
variable {X : Type*}


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornRecover_product_state (f : X → ℂ) (e0 : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ = 1) (he0 : ∑ z, ‖e0 z‖ ^ 2 = 1)
    (v : X → (ZMod N → ℝ)) (t : ℝ) (x : X) :
    bornRecover (v x) t (fun z => productState X f e0 (x, z)) Finset.univ = 1 := by sorry
