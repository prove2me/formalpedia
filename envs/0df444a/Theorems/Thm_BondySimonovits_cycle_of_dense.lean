-- Prove2me | Theorems.Thm_BondySimonovits_cycle_of_dense
-- name    : BondySimonovits.cycle_of_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:04:04.544735+00:00
-- url     : https://prove2.me/theorems/fade0bc0-f6c9-447f-94ae-430ddf6c8519
-- title:
--   Bondy Simonovits: cycle of dense
-- statement:
--   **Key lemma.** A minimal subset of two consecutive BFS layers with minimum degree `≥ 2k`
--   contains (together with the BFS tree) a cycle of length exactly `2k`.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L186-L300
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L186-L300

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]

theorem BondySimonovits.cycle_of_dense (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) (x : V) (k i : ℕ)
    (hk : 2 ≤ k) (hik : i + 1 ≤ k) (Y : Finset V)
    (hYL : ∀ v ∈ Y, K.Reachable x v ∧ (K.dist x v = i ∨ K.dist x v = i + 1))
    (hne : Y.Nonempty) (hdeg : ∀ u ∈ Y, 2 * k ≤ (Y.filter (K.Adj u)).card)
    (hmin : ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', 2 * k ≤ (Y'.filter (K.Adj u)).card) → Y' = Y) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = 2 * k := by sorry
