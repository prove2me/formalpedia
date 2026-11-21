-- Prove2me | Theorems.Thm_Champernowne_tendsto_countOccurrences_champPrefix_div
-- name    : Champernowne.tendsto_countOccurrences_champPrefix_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:21.39786+00:00
-- url     : https://prove2.me/theorems/6ae66119-e823-4777-8a82-20c79484ee91
-- title:
--   Champernowne: tendsto count Occurrences champ Prefix div
-- statement:
--   Every nonempty block `w` (digits `< b`)
--   occurs in the base-`b` Champernowne stream with asymptotic frequency
--   `b⁻ᵏ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L247-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L247-L266

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

theorem Champernowne.tendsto_countOccurrences_champPrefix_div {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    Tendsto (fun n => (countOccurrences w (champPrefix b n) : ℝ) / n)
      atTop (𝓝 (((b : ℝ) ^ w.length)⁻¹)) := by sorry
