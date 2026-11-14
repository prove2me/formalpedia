-- Prove2me | Theorems.Thm_BilateralProfitLB_claim_7_2
-- name    : BilateralProfitLB.claim_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:07.057795+00:00
-- url     : https://prove2.me/theorems/992735e1-d3b3-4d44-a991-263e06bc61a4
-- title:
--   Claim 7.2 — properties of the bump $\rho(u)=16u^2(1-u)^2\mathbb 1\{u\in[0,1]\}$
-- statement:
--   Let $\rho(u)=16u^2(1-u)^2\,\mathbb 1\{u\in[0,1]\}$ for $u\in\mathbb R$. Then:
--
--   1. $\rho$ is twice continuously differentiable on $(0,1)$;
--   2. $\rho$ has a unique maximum, equal to $1$, at $u=1/2$;
--   3. $\rho$ is differentiable at $0$ and $1$ with $\rho'(0)=\rho'(1)=0$;
--   4. $\rho$ is differentiable on $\mathbb R$ and $\|\rho'\|_\infty\le4$;
--   5. at every $u\notin\{0,1\}$, $\rho'$ is differentiable and $|\rho''(u)|\le32$.
--
--   The bump is scaled by $w^2/2$ and placed on each interval $I_j$ to build the perturbed buyers $\mathcal D_j$; these bounds on its derivatives are what keep the perturbed distributions regular.
--
--   **Formalization Note** $\rho''$ does not exist at $0$ and $1$ (it jumps from $0$ to $32$), so the second-derivative bound is stated at all other points, together with the existence of $\rho''$ there.
--
--   Differences from the source:
--   - encoding: $\|\rho''\|_\infty\le32$ → $|\rho''(u)|\le32$ and $\rho'$ differentiable at every $u\ne0,1$; reason: $\rho''$ does not exist at $0,1$, where Lean's derivative would be a junk value
--   - encoding: $\|\rho'\|_\infty\le4$ → $\rho$ differentiable on $\mathbb R$ and $|\rho'(u)|\le4$ for all $u$; reason: makes the derivative genuine; same content
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 7.2, p.50 (PDF 52)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction

namespace BilateralProfitLB

/-- **Claim 7.2**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.50
(PDF 52): the bump `ρ(u) = 16u²(1 − u)² · 1{u ∈ [0,1]}` is twice continuously differentiable in
`(0, 1)`, has unique maximum `1` at `u = 1/2`, its first derivative vanishes at `0` and `1`, and
`‖ρ′‖_∞ ≤ 4`, `‖ρ″‖_∞ ≤ 32`.

**Formalization Note.** `ρ` is a function on `ℝ`. "Unique maximum 1 at 1/2" is `ρ ≤ 1`
everywhere, `ρ(1/2) = 1`, and `ρ(u) = 1 → u = 1/2`. The vanishing of `ρ′` at `0` and `1` is
`HasDerivAt ρ 0 0` and `HasDerivAt ρ 0 1` (both one-sided derivatives vanish). `‖ρ′‖_∞ ≤ 4` is
stated together with differentiability of `ρ` on all of `ℝ`, so `deriv ρ` is the genuine
derivative. `ρ″` does not exist at `0` and `1` (it jumps from `0` to `32`); the bound on `ρ″` is
stated at every other point, where `ρ′` is differentiable (also stated). -/
theorem claim_7_2 :
    ContDiffOn ℝ 2 rho (Set.Ioo 0 1) ∧
      ((∀ u, rho u ≤ 1) ∧ rho (1 / 2) = 1 ∧ ∀ u, rho u = 1 → u = 1 / 2) ∧
      (HasDerivAt rho 0 0 ∧ HasDerivAt rho 0 1) ∧
      (Differentiable ℝ rho ∧ ∀ u, |deriv rho u| ≤ 4) ∧
      (∀ u, u ≠ 0 → u ≠ 1 →
        DifferentiableAt ℝ (deriv rho) u ∧ |deriv (deriv rho) u| ≤ 32) := by sorry

end BilateralProfitLB
