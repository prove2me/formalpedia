-- Prove2me | Theorems.Thm_ApproxIC_Rounding_proposition_1
-- name    : ApproxIC.Rounding.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:04.880372+00:00
-- url     : https://prove2.me/theorems/295a0197-f12c-4002-aca3-7bf602a54819
-- title:
--   Proposition 1, p. 15 — upper bound via rounding: Π⋆(M(ε)) − Π⋆(M(0)) = O(ε^{1/2})
-- statement:
--   **Proposition 1 (Upper Bound via Rounding).** Consider a seller selling one item to one buyer whose value has a density $f$ supported in $S=[0,\bar v]$, and let $\mathcal M(\varepsilon)$ be the set of individually rational, $\varepsilon$-incentive compatible direct mechanisms, $\Pi(m)=\mathbb E_v[t(v)]$ the revenue of a mechanism and $\Pi^\star(\mathcal M(\varepsilon))=\sup_{m\in\mathcal M(\varepsilon)}\Pi(m)$. Then
--   $$\Pi^\star(\mathcal M(\varepsilon))-\Pi^\star(\mathcal M(0))=\mathcal O(\varepsilon^{1/2}).$$
--   Explicitly: there exist constants $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ and every $m\in\mathcal M(\varepsilon)$,
--   $$\Pi(m)-\Pi^\star(\mathcal M(0))\;\le\;C\sqrt{\varepsilon}.$$
--
--   The result says that allowing the buyer to be an $\varepsilon$-optimizer can raise the seller's optimal revenue by at most order $\sqrt\varepsilon$. It is the benchmark that the paper's instance-dependent bounds of order $\varepsilon^{\alpha/(2\alpha-1)}$ improve upon.
--
--   **Formalization Note** The $\mathcal O$-notation is the paper's (p. 13): $C$ and $\varepsilon_0$ may depend on the distribution and are chosen before $\varepsilon$. The bound is stated for every $m\in\mathcal M(\varepsilon)$ rather than for the supremum; the two are equivalent because the revenue image of $\mathcal M(\varepsilon)$ is nonempty and bounded above, so $\Pi^\star(\mathcal M(\varepsilon))$ is a genuine supremum. $\Pi^\star(\mathcal M(0))$ is kept as the supremum over $\mathcal M(0)$, as printed. $\varepsilon^{1/2}$ is written `Real.sqrt ε`. Mechanisms are required to be measurable.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 15, Proposition 1 (O-notation of p. 13; proof in Appendix A, p. 38)

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

namespace ApproxIC.Rounding

/-- Proposition 1 (Upper Bound via Rounding), p. 15: `Π⋆(M(ε)) − Π⋆(M(0)) = O(ε^{1/2})`, with the
O-notation of p. 13: there are `C > 0` and `ε₀ > 0` (depending on the distribution) such that every
`m ∈ M(ε)` satisfies `Π(m) − Π⋆(M(0)) ≤ C √ε` for all `ε ∈ (0, ε₀]`. -/
theorem proposition_1 (M : Model) (hM : M.Standing) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∀ m ∈ Mset M ε,
      revenue M m - optRev M 0 ≤ C * Real.sqrt ε := by sorry

end ApproxIC.Rounding
