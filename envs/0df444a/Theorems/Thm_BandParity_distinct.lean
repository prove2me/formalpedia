-- Prove2me | Theorems.Thm_BandParity_distinct
-- name    : BandParity.distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:19.383817+00:00
-- url     : https://prove2.me/theorems/d94feae5-e08e-42cc-afcc-5d364995a89b
-- title:
--   Band Parity: distinct
-- statement:
--   The values `0, 1, i, -1, -i` are pairwise distinct (as `simp` lemmas).
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L72-L78
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L72-L78

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.distinct :
    ((1 : GaussianInt) = gi ↔ False) ∧ ((1 : GaussianInt) = -1 ↔ False) ∧
    ((1 : GaussianInt) = -gi ↔ False) ∧ (gi = 1 ↔ False) ∧ (gi = -1 ↔ False) ∧
    (gi = -gi ↔ False) ∧ ((-1 : GaussianInt) = 1 ↔ False) ∧ ((-1 : GaussianInt) = gi ↔ False) ∧
    ((-1 : GaussianInt) = -gi ↔ False) ∧ (-gi = 1 ↔ False) ∧ (-gi = gi ↔ False) ∧
    (-gi = (-1 : GaussianInt) ↔ False) := by sorry
