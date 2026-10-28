-- Prove2me | Theorems.Thm_Erdos195_epsLt_star
-- name    : Erdos195.epsLt_star
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:39:14.061188+00:00
-- url     : https://prove2.me/theorems/5f59adf4-b2cb-41d0-b984-67c8d6b1913d
-- title:
--   $\varepsilon$-orders satisfy Ho's identity $(\ast)$
-- statement:
--   For every $\varepsilon$, all integers $a$ and all $r\neq0$,
--
--   $$a\prec_\varepsilon a+r \iff a+2r\prec_\varepsilon a+3r.$$
--
--   This is the $\mathbb{Z}$-version of identity (1) in Ho's paper ($a\triangleleft b\iff c\triangleleft d$ for a $4$-term progression $a,b,c,d$), which drives both of Ho's lemmas.
--
--   **Formalization Note** `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   B. S. Ho, arXiv:2609.12780, §2, identity (1); here over ℤ for all ε

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_star (ε : ℕ → Bool) : Star (epsLt ε) := by sorry

end Erdos195
