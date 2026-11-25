-- Prove2me | Theorems.Thm_ErdosGirth_exists_girth_chromaticNumber
-- name    : ErdosGirth.exists_girth_chromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:09.961792+00:00
-- url     : https://prove2.me/theorems/7bf00386-1366-4f7f-bd43-3d6abc264f1d
-- title:
--   Erdos Girth: exists girth chromatic Number
-- statement:
--   **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
--   than `g` and chromatic number greater than `k`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L82-L86
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L82-L86

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by sorry
