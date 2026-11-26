-- Prove2me | Theorems.Thm_Erdos266_m_ne_zero
-- name    : Erdos266.m_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:10.038886+00:00
-- url     : https://prove2.me/theorems/6bff3823-a3c2-5835-ac6c-4f273fecdcbf
-- title:
--   Erdos266: m ne zero
-- statement:
--   The coefficients are nonzero (this is where injectivity of the
--   enumeration is used); in particular the diagonal ones, which the triangular
--   induction divides by.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L43-L45
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L43-L45

module
public import Definitions.Def_Erdos266_Enumeration
public import Definitions.Def_Erdos266_Defs
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.m_ne_zero (i j : ℕ) : m i j ≠ 0 := by sorry
