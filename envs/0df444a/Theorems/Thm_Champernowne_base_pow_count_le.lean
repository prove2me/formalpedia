-- Prove2me | Theorems.Thm_Champernowne_base_pow_count_le
-- name    : Champernowne.base_pow_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:17.063879+00:00
-- url     : https://prove2.me/theorems/52f5d9e5-c44d-49af-be3d-c79fa4fbd373
-- title:
--   Champernowne: base pow count le
-- statement:
--   The Champernowne construction uses the base pow count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L97-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L97-L103

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

theorem Champernowne.base_pow_count_le {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by sorry
