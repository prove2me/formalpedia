-- Prove2me | Theorems.Thm_Erdos195_epsLt_isStrictTotalOrder
-- name    : Erdos195.epsLt_isStrictTotalOrder
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:35:51.756448+00:00
-- url     : https://prove2.me/theorems/983e7a48-629c-4122-83ab-31751b261fb6
-- title:
--   $\varepsilon$-orders are strict total orders on $\mathbb{Z}$
-- statement:
--   For every $\varepsilon:\mathbb{N}\to\{\mathrm{true},\mathrm{false}\}$, the relation $\prec_\varepsilon$ on $\mathbb{Z}$ is a strict total order: it is irreflexive and transitive, and any two distinct integers are comparable.
--
--   $$\forall x\neq y:\ x\prec_\varepsilon y \ \lor\ y\prec_\varepsilon x, \qquad x\prec_\varepsilon y\prec_\varepsilon z\implies x\prec_\varepsilon z.$$
--
--   Completion orders built from $\prec_\varepsilon$ are therefore genuine linear orders.
--
--   **Formalization Note** `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   B. S. Ho, arXiv:2609.12780, §2 (order ◁ = case ε ≡ true on ℕ); Ardal–Brown–Jungić binary chaotic order; generalisation to ℤ and arbitrary ε is new to this mission

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_isStrictTotalOrder (ε : ℕ → Bool) : IsStrictTotalOrder ℤ (epsLt ε) := by sorry

end Erdos195
