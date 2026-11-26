-- Prove2me | Theorems.Thm_Erdos266_mseq_cond
-- name    : Erdos266.mseq_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:54.671217+00:00
-- url     : https://prove2.me/theorems/f94f4a20-f98b-574b-8004-b0557e2d7783
-- title:
--   Erdos266: mseq cond
-- statement:
--   The domination condition available from step `mseq d` on (for `d ≥ 1`):
--   the lattice-step error at dimension `d` fits inside the next invariant
--   radius, measured with the envelope `εA (d + 1)`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L119-L126
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L119-L126

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.mseq_cond (d : ℕ) : ∀ k, mseq (d + 1) ≤ k → ∀ i : ℕ, i < d + 1 →
    DL (d + 1) * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
      ≤ εA (d + 2) * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by sorry
