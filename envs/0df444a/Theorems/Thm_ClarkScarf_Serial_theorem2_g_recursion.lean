-- Prove2me | Theorems.Thm_ClarkScarf_Serial_theorem2_g_recursion
-- name    : ClarkScarf.Serial.theorem2_g_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:49.82544+00:00
-- url     : https://prove2.me/theorems/89d49e32-0a65-4adc-bf99-f33b228514fb
-- title:
--   Theorem 2 (p. 484) — the gₙ of (16) are given by recursion (26) with the augmented cost L̃ + Λ
-- statement:
--   In the two-installation model, suppose that for every $n\ge3$ periods remaining the isolated installation-1 problem (15) has a critical number $\bar x_n$. Define $g_1=\tilde L$ and, for $n\ge2$,
--   $$g_n(x_2)=\inf_{z\ge0}\Big\{c(z)+\tilde L(x_2)+\Lambda_n(x_2)+\alpha\int_0^\infty g_{n-1}(x_2+z-t)\varphi(t)\,dt\Big\}\qquad(26)$$
--   with $\Lambda_n$ of (25) (and $\Lambda_2\equiv0$). Then for every $n\ge1$ and every state with $x_1+w_1\le x_2$,
--   $$C_n(x_1,w_1,x_2)=\hat C_n(x_1,w_1)+g_n(x_2).$$
--
--   So the echelon-2 problem is an ordinary single-installation inventory problem whose one-period cost is the natural cost $\tilde L$ augmented by $\Lambda_n$; solving it yields the optimal system orders.
--
--   **Formalization Note** The paper's (26) writes $\Lambda(x_2)$ for $\Lambda_n(x_2)$. Rather than asserting that the $g$ of Theorem 1 satisfies (26), which would quantify over an object the page constructs, the statement defines $g_n$ by (26) (`gClark`, with $g_0\equiv0$, which gives $g_1=\tilde L$) and asserts (16) for it. The critical numbers are hypotheses, as in the paper; for $n\le2$ none is needed because no shipment placed then arrives within the horizon.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 484, Theorem 2, eqs. (25)-(26)

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Theorem 2, p. 484: given critical numbers `x̄_{n+1}` of the isolated problem for every
`n + 1 ≥ 3` periods remaining, the functions `g_n` of (26), with `g_1 = L̃` and `Λ` of (25),
satisfy `C_n(x₁, w₁, x₂) = Ĉ_n(x₁, w₁) + g_n(x₂)` for every `n ≥ 1` and `x₁ + w₁ ≤ x₂`. -/
theorem theorem2_g_recursion (M : Model) (xbar : ℕ → ℝ)
    (hxbar : ∀ n : ℕ, 2 ≤ n → M.IsCriticalNumber n (xbar (n + 1))) :
    ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
      M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + M.gClark xbar n x₂ := by sorry

end ClarkScarf.Serial
