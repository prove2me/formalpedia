-- Prove2me | Theorems.Thm_Erdos1219_sum_aleph_eq_aleph_omega
-- name    : Erdos1219.sum_aleph_eq_aleph_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:52.368468+00:00
-- url     : https://prove2.me/theorems/b2fccacc-94d1-4a1e-b0a5-7d194ded52df
-- title:
--   Erdos1219: sum aleph eq aleph omega
-- statement:
--   A countable sum of alephs with unbounded indices below `ω` is `ℵ_ω`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L102-L114
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L102-L114

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.sum_aleph_eq_aleph_omega (e : ℕ → ℕ) (he : ∀ N, N ≤ e N) :
    Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u})) = ℵ_ ω := by sorry
