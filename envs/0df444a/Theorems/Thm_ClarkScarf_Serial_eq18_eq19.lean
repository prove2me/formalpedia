-- Prove2me | Theorems.Thm_ClarkScarf_Serial_eq18_eq19
-- name    : ClarkScarf.Serial.eq18_eq19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:15.422566+00:00
-- url     : https://prove2.me/theorems/38250349-4e16-4801-821d-d2f6a6af9a8f
-- title:
--   Eqs. (18)–(19), p. 483 — the system cost when installation 2's stock does or does not bind
-- statement:
--   Fix $n\ge0$. Suppose the decomposition (16) holds with $n$ periods remaining for some function $G$ of echelon stock:
--   $$C_n(x_1,w_1,x_2)=\hat C_n(x_1,w_1)+G(x_2)\quad\text{whenever }x_1+w_1\le x_2,$$
--   and suppose $\bar x$ is a critical number of the isolated installation-1 problem (15) with $n+1$ periods remaining (ordering up to $\bar x$ is optimal at every state). Write
--   $$Z(x_2)=\inf_{z\ge0}\Big\{c(z)+\tilde L(x_2)+\alpha\int_0^\infty G(x_2+z-t)\varphi(t)\,dt\Big\}.$$
--   Then for every state with $x_1+w_1\le x_2$:
--   1. if $x_2\ge\bar x$, then $C_{n+1}(x_1,w_1,x_2)=\hat C_{n+1}(x_1,w_1)+Z(x_2)$ (eq. (18));
--   2. if $x_2<\bar x$, then
--   $$C_{n+1}(x_1,w_1,x_2)=c_1(x_2-x_1-w_1)+L(x_1)+\alpha\int_0^\infty\hat C_n(x_1+w_1-t,\,x_2-x_1-w_1)\varphi(t)\,dt+Z(x_2)\quad\text{(eq. (19))}.$$
--
--   This is the inductive step of the proof of Theorem 1: when echelon-2 stock is ample, installation 1 behaves as in isolation; when it is short, installation 1 ships everything available.
--
--   **Formalization Note** The paper's horizon $n$ is the Lean $n+1$, and its $g_{n-1}$ is the hypothesized $G$. The critical number is a hypothesis, as in the paper, which writes $\bar x_n$ for it.
-- source:
--   Clark and Scarf, Optimal Policies for a Multi-Echelon Inventory Problem, Management Sci. 6(4), 1960, p. 483, eqs. (17)-(19)

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- Eqs. (18)–(19), p. 483: if (16) holds with `n` periods remaining for a function `G` of
echelon stock, and `x̄` is a critical number of the isolated problem with `n + 1` periods
remaining, then with `Z(x₂) = inf_{z ≥ 0} {c(z) + L̃(x₂) + α ∫₀^∞ G(x₂ + z - t) φ(t) dt}`:
for `x₂ ≥ x̄`, `C_{n+1}(x₁, w₁, x₂) = Ĉ_{n+1}(x₁, w₁) + Z(x₂)` (18); for `x₂ < x̄`,
`C_{n+1}(x₁, w₁, x₂) = c₁(x₂ - x₁ - w₁) + L(x₁) + α ∫₀^∞ Ĉ_n(x₁ + w₁ - t, x₂ - x₁ - w₁) φ(t) dt
+ Z(x₂)` (19). -/
theorem eq18_eq19 (M : Model) (n : ℕ) (G : ℝ → ℝ)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (xbar : ℝ) (hxbar : M.IsCriticalNumber n xbar)
    (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    (xbar ≤ x₂ →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.isoCost (n + 1) x₁ w₁ +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) ∧
    (x₂ < xbar →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) := by sorry

end ClarkScarf.Serial
