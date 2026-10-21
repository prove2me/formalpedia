-- Prove2me | Theorems.Thm_FairRandomObject_Bads_prop_14_delta
-- name    : FairRandomObject.Bads.prop_14_delta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:42.617893+00:00
-- url     : https://prove2.me/theorems/191a09b3-dce3-4fe6-a4ff-935deb8d8753
-- title:
--   Proof of Proposition 14, p. 25 — Fair Share gives δ ≥ 0 with ϕ_i(x) ≤ 1/n + δ(x̄/x_i − 1)
-- statement:
--   Let $n\ge2$ and let $\varphi$ be a symmetric API rule for a bad that satisfies Fair Share. Then there is $\delta\ge0$ such that
--   $$\varphi_i(x)\le\frac1n+\delta\Big(\frac{\bar x}{x_i}-1\Big)$$
--   for every $x\in\mathbb R^N_+$ and every agent $i$ with $x_i>0$.
--
--   In the paper, symmetry turns the supporting vector into $\alpha=(\alpha_1,\beta,\dots,\beta)$ with $\beta\ge0$ and $\delta=n\beta$. Bounding $\delta\le1/(n-1)$ and setting $\theta=(n-1)\delta$ then gives (9).
--
--   **Formalization Note** The page says "implies $\alpha\ge0$"; the argument gives $\beta\ge0$, hence $\delta\ge0$. At $x_i=0$ the right-hand side is $+\infty$ in the paper's convention, so only $x_i>0$ is stated.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Proposition 14

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting

namespace FairRandomObject.Bads

open MeasureTheory

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Proposition 14 ("only if"): `α` has the form
`(α_1, β, …, β)` with `β ≥ 0`, and with `δ = nβ`,
`ϕ_i(x) ≤ 1/n + δ (x̄/x_i − 1)` for all `i ∈ N` and `x ∈ ℝ^N_+`.

**Formalization Note.** The page says "implies α ≥ 0"; the argument gives `β ≥ 0`, hence `δ ≥ 0`
is stated. The inequality is stated for `x_i > 0`: at `x_i = 0` the paper's right-hand side is
`+∞` (convention `1/0 = +∞`) and there is nothing to prove. -/
theorem prop_14_delta {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) (hfs : FairShareBad ϕ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ x : Fin n → ℝ, 0 ≤ x → ∀ i, 0 < x i →
      ϕ x i ≤ 1 / n + δ * (mean x / x i - 1) := by sorry

end FairRandomObject.Bads
