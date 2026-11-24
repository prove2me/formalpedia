-- Prove2me | Theorems.Thm_Erdos1219_erdos_1219
-- name    : Erdos1219.erdos_1219
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:49:12.104862+00:00
-- url     : https://prove2.me/theorems/c71e4cf7-b904-4920-b2ca-2b8dbadd4561
-- title:
--   Erdos1219: erdos 1219
-- statement:
--   **Erdős problem #1219** (Erdős–Hajnal–Rado; proved by Shelah).  Let `(n_k)` be an increasing
--   sequence of natural numbers such that `2 ^ ℵ_{n_k}` is strictly increasing and
--   `2 ^ ℵ_{n_0} > ℵ_ω`.  Then `Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Main.lean#L16-L31
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Main.lean#L16-L31

import Definitions.Def_Erdos1219_Canonization
import Definitions.Def_Erdos1219_Main
set_option autoImplicit false
open Cardinal Ordinal
open Erdos1219
universe u

theorem Erdos1219.erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by sorry
