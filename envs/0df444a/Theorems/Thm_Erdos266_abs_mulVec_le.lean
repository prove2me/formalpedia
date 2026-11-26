-- Prove2me | Theorems.Thm_Erdos266_abs_mulVec_le
-- name    : Erdos266.abs_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:02.878641+00:00
-- url     : https://prove2.me/theorems/b001b079-7c14-46d4-95e6-db87cc3c69fa
-- title:
--   Erdos266: abs mul Vec le
-- statement:
--   Row-sum bound for an integer matrix acting on a bounded integer vector,
--   with the bound in `ℝ`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L98-L119
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L98-L119

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix

theorem Erdos266.abs_mulVec_le {d : ℕ} (B : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℤ)
    {zb : ℝ} (hz : ∀ j, |(z j : ℝ)| ≤ zb) (i : Fin d) :
    |((B.mulVec z i : ℤ) : ℝ)|
      ≤ (∑ p : Fin d × Fin d, |((B p.1 p.2 : ℤ) : ℝ)|) * zb := by sorry
