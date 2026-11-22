-- Prove2me | Theorems.Thm_Egrs75_SeedWindow_walk_hits
-- name    : Egrs75.SeedWindow.walk_hits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:53.312518+00:00
-- url     : https://prove2.me/theorems/bad51241-72c4-4021-8bb6-b50d861e4138
-- title:
--   Seed Window: walk hits
-- statement:
--   **Walk lemma (KERNEL-CLEAN).**  If `0 < δ < w₂ − w₁` and the walk
--   `start + t·δ` begins below `w₁`, then its FIRST crossing of `w₁` lands strictly
--   inside `(w₁, w₂)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L64-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean#L64-L91

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75

theorem Egrs75.SeedWindow.walk_hits {δ w₁ w₂ start : ℝ} (hδ0 : 0 < δ) (hδw : δ < w₂ - w₁)
    (hstart : start < w₁) :
    ∃ t : ℕ, 1 ≤ t ∧ w₁ < start + t * δ ∧ start + t * δ < w₂ := by sorry
