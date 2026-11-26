-- Prove2me | Theorems.Thm_Erdos287_buchstab_switch_excess_bound
-- name    : Erdos287.buchstab_switch_excess_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:37:44.134795+00:00
-- url     : https://prove2.me/theorems/6077ffad-ccd8-4f9d-aff4-fe52ed495cae
-- title:
--   Buchstab excess bound for the switched Chen term
-- statement:
--   For positive $a,c$ and $b<1/3$, set $d=(1-b)/(2+1/c)$ and suppose $a\le d\le b$. The weighted integral of the positive excess of $v/(1-2v-b)$ over $c$ on $[a,b]$, with weight $2\log(v/a)\log(b/v)/v^2$, is at most $(1+2c)\log(b/a)(b-d)^3/(3(1-3b)d^3)$.
-- source:
--   Erdős #287, switched term in the mixed Chen sieve bound.

import Mathlib

theorem Erdos287.buchstab_switch_excess_bound (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : b < 1 / 3)
    (had : a ≤ (1 - b) / (2 + 1 / c)) (hdb : (1 - b) / (2 + 1 / c) ≤ b) :
    let d := (1 - b) / (2 + 1 / c)
    2 * (∫ v in a..b, max 0 (v / (1 - 2 * v - b) - c) *
        (Real.log (v / a) * Real.log (b / v) / v ^ 2)) ≤
      (1 + 2 * c) * Real.log (b / a) * (b - d) ^ 3 / (3 * (1 - 3 * b) * d ^ 3) := by sorry
