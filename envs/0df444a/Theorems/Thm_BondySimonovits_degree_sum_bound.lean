-- Prove2me | Theorems.Thm_BondySimonovits_degree_sum_bound
-- name    : BondySimonovits.degree_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:09:29.125873+00:00
-- url     : https://prove2.me/theorems/e6238332-532d-4149-a911-b93e96016b42
-- title:
--   Bondy Simonovits: degree sum bound
-- statement:
--   **Bondy–Simonovits for a `Fintype`**, stated with degree sums: the sum of the degrees is at
--   most `2 (16k + 4) n ^ (1 + 1/k)`.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSFinal.lean#L46-L123
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSFinal.lean#L46-L123

module
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Definitions.Def_BondySimonovitsLib_BSFinal
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.degree_sum_bound (k : ℕ) (hk : 2 ≤ k) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcyc : ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) :
    ((∑ v, (univ.filter (G.Adj v)).card : ℕ) : ℝ) ≤
      2 * (16 * k + 4) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) := by sorry
