-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_digits_vanish
-- name    : CSeparatedNPComplete.SquareReduction.digits_vanish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:08.168228+00:00
-- url     : https://prove2.me/theorems/26ead339-a0f8-4221-9bde-40e44e406cf9
-- title:
--   Square Reduction: digits vanish
-- statement:
--   A bounded perturbation cannot cancel a nonzero highest base-power digit.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L62-L113
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L62-L113

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.digits_vanish {n : ℕ} (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hlarge : (n : ℝ) + C < K ^ 2) (d : Fin n → ℝ)
    (hd : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) (e : ℝ)
    (he : |e| ≤ C * K ^ (2 * n))
    (hzero : (∑ i, d i * K ^ (2 * n + 2 * i.val + 2)) + e = 0) :
    ∀ i, d i = 0 := by sorry
