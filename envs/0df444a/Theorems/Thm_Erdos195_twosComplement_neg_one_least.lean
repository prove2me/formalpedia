-- Prove2me | Theorems.Thm_Erdos195_twosComplement_neg_one_least
-- name    : Erdos195.twosComplement_neg_one_least
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:51:55.783987+00:00
-- url     : https://prove2.me/theorems/13cc1a58-0a3f-43ab-b6fb-25a8922f3a5f
-- title:
--   $-1$ is the least element of the two's-complement order
-- statement:
--   In the $\varepsilon$-order with $\varepsilon\equiv\mathrm{true}$ (the extension to $\mathbb{Z}$ of Ho's order $\triangleleft$), $-1$ precedes every other integer:
--
--   $$\forall y\neq-1:\quad -1\prec_{\mathrm{true}} y.$$
--
--   All two's-complement digits of $-1$ equal $1$, which is the preferred digit at every level.
--
--   **Formalization Note** `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   B. S. Ho, arXiv:2609.12780 §2 (order ◁); extension to ℤ new to this mission

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem twosComplement_neg_one_least (y : ℤ) (hy : y ≠ -1) : epsLt (fun _ => true) (-1) y := by sorry

end Erdos195
