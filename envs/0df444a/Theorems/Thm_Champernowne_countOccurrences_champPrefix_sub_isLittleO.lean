-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_champPrefix_sub_isLittleO
-- name    : Champernowne.countOccurrences_champPrefix_sub_isLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:20.771375+00:00
-- url     : https://prove2.me/theorems/ef64db56-1ebe-4207-819a-fbf60c9fd248
-- title:
--   Champernowne: count Occurrences champ Prefix sub is Little O
-- statement:
--   `countOccurrences w (champPrefix b n) −
--   n/b^k = o(n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L192-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L192-L242

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

theorem Champernowne.countOccurrences_champPrefix_sub_isLittleO {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (fun n => (countOccurrences w (champPrefix b n) : ℝ) - n / (b : ℝ) ^ w.length)
      =o[atTop] (fun n => (n : ℝ)) := by sorry
