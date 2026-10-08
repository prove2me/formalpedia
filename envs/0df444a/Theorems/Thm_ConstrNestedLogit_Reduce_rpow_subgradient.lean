-- Prove2me | Theorems.Thm_ConstrNestedLogit_Reduce_rpow_subgradient
-- name    : ConstrNestedLogit.Reduce.rpow_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:09.658985+00:00
-- url     : https://prove2.me/theorems/03f66d2d-d333-4a99-8212-453d1cbb19f6
-- title:
--   §3, p. 13 — subgradient inequality $u^{\gamma} \le \hat u^{\gamma-1}(\gamma u + \alpha(1-\gamma)\hat u)$ for $\gamma \in (0,1]$, $\alpha \ge 1$
-- statement:
--   Let $\gamma \in (0, 1]$ and $\alpha \ge 1$. For every $u \ge 0$ and every $\hat u > 0$,
--   $$u^{\gamma} \le \hat u^{\gamma} + \gamma\, \hat u^{\gamma - 1}(u - \hat u) = \hat u^{\gamma - 1}\big(\gamma u + (1 - \gamma)\hat u\big) \le \hat u^{\gamma - 1}\big(\gamma u + \alpha (1 - \gamma)\hat u\big).$$
--   The first inequality is the subgradient (tangent-line) inequality of the concave function $u \mapsto u^\gamma$ at $\hat u$; the last uses $\alpha \ge 1$ and $\gamma \le 1$.
--
--   In the proof of Lemma 3 this chain is applied with $u = V_i(S^*_i)$ and $\hat u = V_i(\hat S_i)$ to compare the nest weights $V_i^{\gamma_i}$ of the optimal and the approximate assortment.
--
--   **Formalization Note** The paper writes "for all $u, \hat u \in \Re_+$". At $\hat u = 0$ and $\gamma < 1$ the factor $\hat u^{\gamma - 1}$ is infinite on paper, while Lean's `Real.rpow` gives $0^{\gamma-1} = 0$, so the literal statement would be false in Lean. The paper applies the inequality only after showing $\hat V_i > 0$, so the statement requires $\hat u > 0$. Powers are `Real.rpow`.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 13, proof of Lemma 3 (subgradient inequality)

import Mathlib

namespace ConstrNestedLogit.Reduce

/-- The subgradient (tangent-line) inequality of `u ↦ u^γ` for `γ ∈ (0, 1]`, followed by the
identity and the bound with `α ≥ 1` of p. 13 (proof of Lemma 3), at a base point `û > 0`. -/
theorem rpow_subgradient (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα : 1 ≤ α)
    (u û : ℝ) (hu : 0 ≤ u) (hû : 0 < û) :
    u ^ γ ≤ û ^ γ + γ * û ^ (γ - 1) * (u - û) ∧
    û ^ γ + γ * û ^ (γ - 1) * (u - û) = û ^ (γ - 1) * (γ * u + (1 - γ) * û) ∧
    û ^ (γ - 1) * (γ * u + (1 - γ) * û) ≤ û ^ (γ - 1) * (γ * u + α * (1 - γ) * û) := by sorry

end ConstrNestedLogit.Reduce
