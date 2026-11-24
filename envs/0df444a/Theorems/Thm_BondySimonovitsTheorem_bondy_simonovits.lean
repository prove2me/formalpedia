-- Prove2me | Theorems.Thm_BondySimonovitsTheorem_bondy_simonovits
-- name    : BondySimonovitsTheorem.bondy_simonovits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:21:41.940525+00:00
-- url     : https://prove2.me/theorems/6e13c801-ff06-4aa5-8130-34a7fca0c042
-- title:
--   Bondy Simonovits Theorem: bondy simonovits
-- statement:
--   **The even cycle theorem (Bondy–Simonovits 1974).**
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/Solution.lean#L32-L36
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/Solution.lean#L32-L36

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BondySimonovits
public import Definitions.Def_BondySimonovitsLib_Solution
public import Theorems.Thm_BondySimonovits_bondy_simonovits

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BondySimonovitsTheorem
universe u

theorem BondySimonovitsTheorem.bondy_simonovits (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) →
      (G.edgeSet.ncard : ℝ) ≤ C * (Nat.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by sorry
