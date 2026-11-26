-- Prove2me | Theorems.Thm_Erdos266_latt
-- name    : Erdos266.latt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:41.1232+00:00
-- url     : https://prove2.me/theorems/f03149b4-3ef7-4fd3-8f15-f4212066fb65
-- title:
--   Erdos266: latt
-- statement:
--   The lattice lemma, with its constants named.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L58-L67
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L58-L67

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.latt (d : ℕ) :
    ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ εL d * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ DL d * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) := by sorry
