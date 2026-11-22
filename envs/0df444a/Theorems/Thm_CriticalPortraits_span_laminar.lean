-- Prove2me | Theorems.Thm_CriticalPortraits_span_laminar
-- name    : CriticalPortraits.span_laminar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:13.644845+00:00
-- url     : https://prove2.me/theorems/7376c0d1-c668-4ed6-8ff6-6522ed6cc53a
-- title:
--   Critical Portraits: span laminar
-- statement:
--   **Lemma 2 (span laminarity).** Distinct blocks of a portrait have laminar spans: nested or
--       disjoint (no proper `.val`-overlap `spanLo A < spanLo B < spanHi A < spanHi B`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L570-L581
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L570-L581

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.span_laminar {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {A B : Finset (ZMod (d * m))} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ¬ (spanLo A hAne < spanLo B hBne ∧ spanLo B hBne < spanHi A hAne ∧
       spanHi A hAne < spanHi B hBne) := by sorry
