-- Prove2me | Theorems.Thm_Erdos919_erdos919_aleph1_iff
-- name    : Erdos919.erdos919_aleph1_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:38.550048+00:00
-- url     : https://prove2.me/theorems/fee7e10e-739f-426a-aa77-4021cd1b20d8
-- title:
--   Erdos919: erdos919 aleph1 iff
-- statement:
--   The `ℵ₁` version is equivalent to `ℵ₂` failing countable chromatic compactness.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L567-L591
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L567-L591

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section

theorem Erdos919.erdos919_aleph1_iff :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by sorry
