-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_recurrenceCertificate_mass
-- name    : BooleanIsoperimetry.CoherentGap.recurrenceCertificate_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:06.890176+00:00
-- url     : https://prove2.me/theorems/9f5367f9-5bc2-42fa-8f4f-b2fdba9a0b55
-- title:
--   Coherent Gap: recurrence Certificate mass
-- statement:
--   Every recurrence certificate has mass equal to its Conway--Guy-style
--   reference coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L530-L536
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/CoherentGap.lean#L530-L536

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.recurrenceCertificate_mass (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) {n : ℕ}
    (coordinate : Fin n) :
    ((recurrenceCertificates tower recurrence n coordinate).relations.length : ℤ) =
      tower.weights n coordinate := by sorry
