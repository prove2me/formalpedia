-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_truncate_le
-- name    : Auto.aux_eLpNorm_truncate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:21.587796+00:00
-- url     : https://prove2.me/theorems/e00e1e5b-e9ab-4888-80ba-0f7d6a7391ec
-- title:
--   Auto: aux e Lp Norm truncate le
-- statement:
--   The Auto construction uses the aux e Lp Norm truncate le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2197-L2202
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2197-L2202

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_eLpNorm_truncate_le {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) (p : ℝ≥0∞) :
    eLpNorm (aux_truncate A F) p Measure.count ≤ eLpNorm F p Measure.count := by sorry
