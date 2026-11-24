-- Prove2me | Theorems.Thm_BondySimonovits_bfs_bound
-- name    : BondySimonovits.bfs_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:09:13.702802+00:00
-- url     : https://prove2.me/theorems/6b3cd142-02c8-433b-ab9d-9fc8e2046702
-- title:
--   Bondy Simonovits: bfs bound
-- statement:
--   **Layer growth.** The `k`-th layer has at least `(d / (2k) - 3) ^ k` vertices.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L200-L235
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L200-L235

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
omit [DecidableEq V]

theorem BondySimonovits.bfs_bound (x : V) (k : ℕ) (hk : 2 ≤ k)
    (hcyc : ∀ (v : V) (p : K.Walk v v), p.IsCycle → p.length ≠ 2 * k) (d : ℕ)
    (hdeg : ∀ v, K.Reachable x v → d ≤ (univ.filter (K.Adj v)).card) (hdk : 8 * k ≤ d) :
    ((d : ℝ) / (2 * k : ℕ) - 3) ^ k ≤ Fintype.card V := by sorry
