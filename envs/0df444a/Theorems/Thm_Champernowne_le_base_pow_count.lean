-- Prove2me | Theorems.Thm_Champernowne_le_base_pow_count
-- name    : Champernowne.le_base_pow_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:12.649211+00:00
-- url     : https://prove2.me/theorems/b7732b33-8ebf-48ff-b627-55c87e2c4487
-- title:
--   Champernowne: le base pow count
-- statement:
--   The Champernowne construction uses the le base pow count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L105-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L105-L111

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology

theorem Champernowne.le_base_pow_count {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ champM b n := by sorry
