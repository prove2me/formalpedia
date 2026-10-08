-- Prove2me | Theorems.Thm_ClarkScarf_Serial_lambda_eq25
-- name    : ClarkScarf.Serial.lambda_eq25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:24.928874+00:00
-- url     : https://prove2.me/theorems/0c3cab8d-7fc5-4562-846b-64a316fc007a
-- title:
--   Eqs. (21)–(25), pp. 483–484 — Λₙ(x₁, w₁, x₂) depends on x₂ alone and equals (25)
-- statement:
--   Let $n\ge3$ be the number of periods remaining, and let $\bar x_n$ be a critical number of the isolated installation-1 problem (15) for $n$ periods. For a state with $x_1+w_1\le x_2<\bar x_n$, the extra cost (21) that installation 1 incurs because echelon 2 cannot supply its target,
--   $$\Lambda_n(x_1,w_1,x_2)=c_1(x_2-x_1-w_1)+L(x_1)+\alpha\int_0^\infty\hat C_{n-1}(x_1+w_1-t,\,x_2-x_1-w_1)\varphi(t)\,dt-\hat C_n(x_1,w_1),$$
--   depends on $x_2$ alone, and equals (25):
--   $$\Lambda_n(x_2)=c_1(x_2-\bar x_n)+\alpha^2\int_0^\infty\!\!\int_0^\infty[L(x_2-t-y)-L(\bar x_n-t-y)]\varphi(t)\varphi(y)\,dy\,dt+\alpha\int_0^\infty[f_{n-1}(x_2-t)-f_{n-1}(\bar x_n-t)]\varphi(t)\,dt.$$
--
--   This identity is what makes the system cost split into the isolated cost plus a function of echelon stock, and it gives the explicit penalty that echelon 2 adds to its natural cost.
--
--   **Formalization Note** The Lean index $n$ is the paper's $n-1$, so the hypothesis $2\le n$ is the paper's $n\ge3$, the range in which (6) applies to $\hat C_{n-1}$. The page's expansion of $\hat C_{n-1}$ before (24) prints $f_n$ where $f_{n-1}$ is meant, as (24) and (25) confirm; the Lean uses $f_{n-1}$.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, pp. 483-484, eqs. (21)-(25)

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (21)–(25), pp. 483–484: with `n + 1 ≥ 3` periods remaining, critical number `x̄` and
`x₁ + w₁ ≤ x₂ < x̄`, the quantity `Λ` of (21) depends on `x₂` alone and equals (25). -/
theorem lambda_eq25 (M : Model) (n : ℕ) (hn : 2 ≤ n) (xbar : ℝ)
    (hxbar : M.IsCriticalNumber n xbar) (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) (hlt : x₂ < xbar) :
    M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) -
        M.isoCost (n + 1) x₁ w₁ =
      M.c1 * (x₂ - xbar) +
        M.α ^ 2 * (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) +
        M.α * ∫ t in Ioi (0 : ℝ), (M.fLag n (x₂ - t) - M.fLag n (xbar - t)) * M.φ t := by sorry

end ClarkScarf.Serial
