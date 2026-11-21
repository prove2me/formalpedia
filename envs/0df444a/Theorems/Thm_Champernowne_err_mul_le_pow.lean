-- Prove2me | Theorems.Thm_Champernowne_err_mul_le_pow
-- name    : Champernowne.err_mul_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:18.796183+00:00
-- url     : https://prove2.me/theorems/d5b10598-030e-4560-ad54-8be089e084a8
-- title:
--   Champernowne: err mul le pow
-- statement:
--   The error dominates its own budget: `E(n)·(b-1)(M−1) ≤ E'·n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L114-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L114-L128

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology

theorem Champernowne.err_mul_le_pow {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * (champM b n - 1))
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by sorry
