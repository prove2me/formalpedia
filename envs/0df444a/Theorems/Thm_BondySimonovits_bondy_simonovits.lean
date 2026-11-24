-- Prove2me | Theorems.Thm_BondySimonovits_bondy_simonovits
-- name    : BondySimonovits.bondy_simonovits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:07:31.053367+00:00
-- url     : https://prove2.me/theorems/444b4aef-1249-4975-8ae8-062ec8113cdd
-- title:
--   Bondy Simonovits: bondy simonovits
-- statement:
--   **The even cycle theorem (Bondy–Simonovits 1974).**
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BondySimonovits.lean#L31-L47
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BondySimonovits.lean#L31-L47

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSFinal
public import Definitions.Def_BondySimonovitsLib_BondySimonovits
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BondySimonovits
universe u

theorem BondySimonovits.bondy_simonovits (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) →
      (G.edgeSet.ncard : ℝ) ≤ C * (Nat.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by sorry
