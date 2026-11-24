-- Prove2me | Theorems.Thm_BondySimonovits_exists_minimal_dense
-- name    : BondySimonovits.exists_minimal_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:02:58.667994+00:00
-- url     : https://prove2.me/theorems/e6fa501b-f256-48ea-8b76-8ad51d1f4733
-- title:
--   Bondy Simonovits: exists minimal dense
-- statement:
--   If there are many edges, there is a nonempty subset of minimum degree `≥ D`, which can be
--   chosen minimal.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L130-L148
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L130-L148

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.exists_minimal_dense (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (X : Finset V)
    (hX : 2 * D * X.card < ecount K X X + 2 * X.card) :
    ∃ Y ⊆ X, Y.Nonempty ∧ (∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card) ∧
      ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', D ≤ (Y'.filter (K.Adj u)).card) → Y' = Y := by sorry
