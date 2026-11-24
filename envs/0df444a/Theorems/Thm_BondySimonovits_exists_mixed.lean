-- Prove2me | Theorems.Thm_BondySimonovits_exists_mixed
-- name    : BondySimonovits.exists_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:04:15.501791+00:00
-- url     : https://prove2.me/theorems/be47b80f-653e-4336-bfe0-a0f54f787750
-- title:
--   Bondy Simonovits: exists mixed
-- statement:
--   In a minimal dense subset of two consecutive layers, a non-constant property of the lower
--   layer is witnessed by a vertex with neighbours of both kinds.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L30-L70
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L30-L70

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]

theorem BondySimonovits.exists_mixed (lev : V → ℕ) (i D : ℕ) (Y : Finset V)
    (hYlev : ∀ v ∈ Y, lev v = i ∨ lev v = i + 1)
    (hYadj : ∀ u ∈ Y, ∀ v ∈ Y, K.Adj u v → lev u ≠ lev v)
    (hmin : ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', D ≤ (Y'.filter (K.Adj u)).card) → Y' = Y)
    (hdeg : ∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card)
    (χ : V → Prop) (s0 s1 : V) (hs0 : s0 ∈ Y ∧ lev s0 = i) (hs1 : s1 ∈ Y ∧ lev s1 = i)
    (hχ0 : χ s0) (hχ1 : ¬ χ s1) :
    ∃ w ∈ Y, ∃ a b, (a ∈ Y ∧ lev a = i) ∧ (b ∈ Y ∧ lev b = i) ∧ K.Adj w a ∧ K.Adj w b ∧
      χ a ∧ ¬ χ b := by sorry
