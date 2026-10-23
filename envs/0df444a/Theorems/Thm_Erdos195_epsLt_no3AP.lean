-- Prove2me | Theorems.Thm_Erdos195_epsLt_no3AP
-- name    : Erdos195.epsLt_no3AP
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T13:36:18.429339+00:00
-- url     : https://prove2.me/theorems/95cc3021-0667-4b17-a320-b7b2ac25866e
-- title:
--   $\varepsilon$-orders contain no monotone $3$-term AP
-- statement:
--   For every $\varepsilon$, there are no integers $a$ and $r\neq0$ with
--
--   $$a\prec_\varepsilon a+r\prec_\varepsilon a+2r.$$
--
--   Since $r$ may be negative, this excludes both increasing and decreasing $3$-term progressions in $\prec_\varepsilon$ order. This is the $\mathbb{Z}$-version of the $3$AP-freeness of Ho's order $\triangleleft$.
--
--   **Formalization Note** `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   B. S. Ho, arXiv:2609.12780, §2 (3AP-freeness of ◁, citing Ardal–Brown–Jungić Theorem 2.2); here over ℤ for all ε

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_no3AP (ε : ℕ → Bool) : No3AP (epsLt ε) := by sorry

end Erdos195
