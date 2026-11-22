-- Prove2me | Theorems.Thm_AbstractLaminar_overlap_imp_nested
-- name    : AbstractLaminar.overlap_imp_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:13.905217+00:00
-- url     : https://prove2.me/theorems/1287cbe6-74f0-4c96-a36f-e6413095baba
-- title:
--   Abstract Laminar: overlap imp nested
-- statement:
--   Two overlapping edges are nested (laminarity).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L105-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L105-L111

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)

theorem AbstractLaminar.overlap_imp_nested {e f : ι} (he : e ∈ fam.E) (hf : f ∈ fam.E)
    (h1 : fam.lo e < fam.hi f) (h2 : fam.lo f < fam.hi e) :
    (fam.lo f ≤ fam.lo e ∧ fam.hi e ≤ fam.hi f) ∨
    (fam.lo e ≤ fam.lo f ∧ fam.hi f ≤ fam.hi e) := by sorry
