-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_balance_identity
-- name    : CSeparatedNPComplete.SquareReduction.balance_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:40.964102+00:00
-- url     : https://prove2.me/theorems/1ce4dc85-e7c1-50bf-98b8-9625522f30ef
-- title:
--   Square Reduction: balance identity
-- statement:
--   The Square Reduction construction uses the balance identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L115-L137
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L115-L137

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.balance_identity {n : ℕ} (a : Fin n → ℕ) (p q : Vec n) :
    dot (Fin.append p q) (values a) - dot (values a) 1 / 2 =
      ∑ i, ((p i + q i - 1) * (base a : ℝ) ^ (2 * n + 2 * i.val + 2) +
        (2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
          (p i + q i - 1) * (lower a i : ℝ) ^ 2)) := by sorry
