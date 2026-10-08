-- Prove2me | Theorems.Thm_CarryRNG_SWB_output_eq_reversed_digits
-- name    : CarryRNG.SWB.output_eq_reversed_digits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:11.709541+00:00
-- url     : https://prove2.me/theorems/6de28556-36c5-44e9-9e42-9cdba85033c4
-- title:
--   §4.3 — generated digits are reversed digits of k/m
-- statement:
--   Let $b\ge2$, $0<s<r$, and $m=b^r-b^s+1$. Take any Method 1 seed $z$ other than $(b-1,\ldots,b-1,1)$ and any endpoint $C\ge r+1$. There is an integer $0\le k<m$, positive exactly when $z$ is not the all-zero seed, such that the generated block $x_{r+1},\ldots,x_C$, read backwards, is the opening block of the base-$b$ expansion of $k/m$:
--   $$
--   x_n=d_{C+1-n}(k/m)\qquad(r+1\le n\le C).
--   $$
--   Here $x_n$ is the newly appended digit after $n-r$ steps, and $d_j$ is the $j$th fractional digit. This precise finite-block form captures the paper’s tableau relation for every seed and every block length; the numerator may depend on $C$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), pp. 470–471, Section 4.3

import Definitions.Def_CarryRNG_SWB_out
import Definitions.Def_CarryRNG_AWC_digit
import Definitions.Def_CarryRNG_SWB_modulus
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Section 4.3: every generated finite block, read backwards, starts the expansion of
a proper fraction with denominator `m = b^r - b^s + 1`. -/
theorem output_eq_reversed_digits (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b)
    (z : CarryRNG.AWC.State b L.r) (hz : z ≠ CarryRNG.AWC.topSeed b L.r hb) (C : ℕ) (hC : L.r + 1 ≤ C) :
    ∃ k : ℕ, k < modulus b L ∧ (0 < k ↔ z ≠ CarryRNG.AWC.zeroSeed b L.r hb) ∧
      ∀ n : ℕ, L.r + 1 ≤ n → n ≤ C →
        out b L hb z n = CarryRNG.AWC.digit b (modulus b L) k (C + 1 - n) := by sorry

end CarryRNG.SWB
