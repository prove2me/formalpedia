-- Prove2me | Theorems.Thm_BondySimonovits_ecount_le_of_degenerate
-- name    : BondySimonovits.ecount_le_of_degenerate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:02:51.762131+00:00
-- url     : https://prove2.me/theorems/6f92831b-13dc-4306-91ed-b3a7d296e80a
-- title:
--   Bondy Simonovits: ecount le of degenerate
-- statement:
--   Degeneracy bound: if every nonempty subset has a vertex of small degree, the number of
--   edges is small.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L111-L126
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L111-L126

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.ecount_le_of_degenerate (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) :
    ∀ X : Finset V, (∀ Y ⊆ X, Y.Nonempty → ∃ u ∈ Y, (Y.filter (K.Adj u)).card < D) →
      ecount K X X + 2 * X.card ≤ 2 * D * X.card := by sorry
