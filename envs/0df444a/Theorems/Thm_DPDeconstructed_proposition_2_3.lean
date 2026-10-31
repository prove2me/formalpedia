-- Prove2me | Theorems.Thm_DPDeconstructed_proposition_2_3
-- name    : DPDeconstructed.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:57.850853+00:00
-- url     : https://prove2.me/theorems/7d2874be-af73-4dbd-838a-83f69bdc96ea
-- title:
--   Proposition 2.3 — $S_\sigma$ has a unique fixed point in $\mathcal G$ iff $T_\sigma$ has one in $\mathcal V$
-- statement:
--   Let $(W_0,W_1)$ be a plan factorization of a dynamic program and $\sigma\in\Sigma$ a feasible policy. The refactored $\sigma$-value operator $S_\sigma=W_0M_\sigma W_1$ has a unique fixed point $g_\sigma$ in $\mathcal G$ if and only if the $\sigma$-value operator $T_\sigma v(x)=H(x,\sigma(x),v)$ has a unique fixed point $v_\sigma$ in $\mathcal V$. Whenever these fixed points exist, they are related by
--
--   $$v_\sigma=M_\sigma W_1g_\sigma\qquad\text{and}\qquad g_\sigma=W_0v_\sigma .$$
--
--   Under Assumption 2.2 this makes the refactored $\sigma$-value functions, and hence $g^*$, well defined, and identifies $g_\sigma$ with $W_0v_\sigma$.
--
--   **Formalization Note** A fixed point of $T_\sigma$ in $\mathcal V$ is a $\sigma$-value function, written with an `EReal` equation because $H$ is extended-real valued. Assumption 2.2 is not assumed.
--
--   Differences from the source:
--   - encoding: T_σ has a unique fixed point v_σ in 𝒱 → there is exactly one σ-value function (v ∈ 𝒱 with v(x) = H(x, σ(x), v) for all x, in EReal); reason: a fixed point of T_σ in 𝒱 is by definition a σ-value function (p.11); H is EReal-valued in Lean
--   - encoding: plan factorization: W₀ defined on 𝒱 with values in 𝒢, W₁ defined on 𝒢 with values in ℋ, and (7) → structure with total maps W₀ on ℝ^X, W₁ on ℝ^F and the single field (7); reason: 𝒢 := W₀𝒱 gives the first condition and (7) gives the second; values off 𝒱 and 𝒢 never enter a statement, so every pair on the page is an instance
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §2.6, p.12, Proposition 2.3

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

namespace DPDeconstructed

open DynProg PlanFactorization

/-- Proposition 2.3, Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, §2.6, p.12: given a dynamic program, a plan factorization `(W₀, W₁)` and
a feasible policy `σ ∈ Σ`, the refactored `σ`-value operator `S_σ = W₀ M_σ W₁` has a unique
fixed point `g_σ` in `𝒢` if and only if `T_σ` has a unique fixed point `v_σ` in `𝒱`
(a unique `σ`-value function). Whenever these fixed points exist, they are related by
`v_σ = M_σ W₁ g_σ` and `g_σ = W₀ v_σ`.

**Formalization Note** A fixed point of `T_σ` in `𝒱` is a `σ`-value function
(`DynProg.IsSigmaValue`, p.6 and p.11). Assumption 2.2 is not assumed: the proposition holds
for every feasible `σ`. -/
theorem proposition_2_3 {X A : Type*} [Nonempty X] {D : DynProg X A}
    (P : PlanFactorization D) (σ : D.Policy) :
    ((∃! g, g ∈ P.calG ∧ P.Sσ σ g = g) ↔ ∃! v, D.IsSigmaValue σ v) ∧
      ∀ (g : D.SA → ℝ) (v : X → ℝ),
        g ∈ P.calG → P.Sσ σ g = g → (∀ g' ∈ P.calG, P.Sσ σ g' = g' → g' = g) →
        D.IsSigmaValue σ v → (∀ v', D.IsSigmaValue σ v' → v' = v) →
        v = D.Mσ σ (P.W₁ g) ∧ g = P.W₀ v := by sorry

end DPDeconstructed
