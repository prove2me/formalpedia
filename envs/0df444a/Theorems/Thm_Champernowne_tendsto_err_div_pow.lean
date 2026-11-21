-- Prove2me | Theorems.Thm_Champernowne_tendsto_err_div_pow
-- name    : Champernowne.tendsto_err_div_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:21.893804+00:00
-- url     : https://prove2.me/theorems/144c16df-3a26-4f84-8b8b-08021c0df7cb
-- title:
--   Champernowne: tendsto err div pow
-- statement:
--   The error sequence is negligible relative to `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L149-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L149-L188

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

theorem Champernowne.tendsto_err_div_pow {b : ℕ} (hb : 1 < b) (w : List ℕ) :
    Tendsto (fun n => (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) / n)
      atTop (𝓝 0) := by sorry
