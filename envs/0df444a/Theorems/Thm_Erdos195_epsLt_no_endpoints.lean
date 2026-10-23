-- Prove2me | Theorems.Thm_Erdos195_epsLt_no_endpoints
-- name    : Erdos195.epsLt_no_endpoints
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T13:39:34.48153+00:00
-- url     : https://prove2.me/theorems/783ba457-049a-45b4-8a74-130cecad73dd
-- title:
--   $\varepsilon$-orders have no endpoints when $\varepsilon$ is not eventually constant
-- statement:
--   Let $\varepsilon:\mathbb{N}\to\{\mathrm{true},\mathrm{false}\}$ be not eventually constant. Then $\prec_\varepsilon$ has neither a least nor a greatest element:
--
--   $$\forall x\in\mathbb{Z}\ \ \exists y,y'\in\mathbb{Z}:\ y\prec_\varepsilon x\prec_\varepsilon y'.$$
--
--   By contrast, the two's-complement order ($\varepsilon\equiv\mathrm{true}$) has least element $-1$, which blocks Ho's method on $\mathbb{Z}$. Orders without endpoints are the candidate replacement.
--
--   **Formalization Note** `epsLt ε x y` is `x ≠ y ∧ (x / 2^k % 2 = 1 ↔ ε k = true)` with `k = padicValInt 2 (y - x)`, i.e. $k=\nu_2(y-x)$; integer division is floor division, so `x / 2^k % 2` is the $k$-th two's-complement digit of $x$.
-- source:
--   New to this mission (motivated by the obstruction for ε ≡ true); setting from B. S. Ho, arXiv:2609.12780 §2

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_no_endpoints (ε : ℕ → Bool) (hε : ¬ ∃ N : ℕ, ∃ b : Bool, ∀ n ≥ N, ε n = b)
    (x : ℤ) : (∃ y, epsLt ε y x) ∧ (∃ y, epsLt ε x y) := by sorry

end Erdos195
