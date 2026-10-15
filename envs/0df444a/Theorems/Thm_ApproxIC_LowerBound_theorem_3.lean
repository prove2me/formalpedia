-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_theorem_3
-- name    : ApproxIC.LowerBound.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:26.245487+00:00
-- url     : https://prove2.me/theorems/1ae1f54c-9543-49ab-9557-d825c882e03e
-- title:
--   Theorem 3, p. 27 — under local α-power envelopes, Π⋆(M(ε)) − Π⋆(M(0)) = Ω(ε^{α/(2α−1)})
-- statement:
--   Let the buyer's value distribution satisfy Assumption 1: it has a density $f$ of bounded variation on $S=[0,\bar v]$. Suppose the revenue function $R(v)=v\bar F(v)$ admits local $\alpha$-power envelopes (Definition 1) at its unique interior maximizer $p^\star$, with constants $\alpha>1$, $\kappa_L,\kappa_U>0$ and neighborhood $\mathcal N_\ell=(p^\star-\ell,p^\star+\ell)$. Then
--   $$\Pi^\star(\mathcal M(\varepsilon))-\Pi^\star(\mathcal M(0))=\Omega\big(\varepsilon^{\alpha/(2\alpha-1)}\big),$$
--   that is, there are constants $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ some $\varepsilon$-IC, individually rational mechanism $m\in\mathcal M(\varepsilon)$ earns
--   $$\Pi(m)\ge\Pi^\star(\mathcal M(0))+C\,\varepsilon^{\alpha/(2\alpha-1)}.$$
--
--   Together with the upper bound of Theorem 1, this pins down the order of the revenue gain from relaxing incentive compatibility to $\varepsilon$-incentive compatibility, up to a logarithmic factor: the gain is supralinear in $\varepsilon$, between order $\varepsilon$ and order $\sqrt\varepsilon$ depending on the curvature $\alpha$ of $R$ at $p^\star$.
--
--   **Formalization Note** The constants $C,\varepsilon_0$ may depend on the distribution and on the envelope constants, but not on $\varepsilon$ (the $\Omega$ notation of p. 13). The existential form is equivalent to the bound on the supremum $\Pi^\star(\mathcal M(\varepsilon))=\sup_{m\in\mathcal M(\varepsilon)}\Pi(m)$, because the revenue image of $\mathcal M(\varepsilon)$ is nonempty and bounded above by $\bar v$. $\Pi^\star(\mathcal M(0))$ is the supremum as printed. Mechanisms are measurable (disclosed in the Setting).
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 27, Theorem 3; p. 13, notation Ω

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting

namespace ApproxIC.LowerBound

open ApproxIC.UpperBound

/-- Theorem 3 (Performance Lower Bound, p. 27): under Assumption 1 and local `α`-power envelopes,
`Π⋆(M(ε)) − Π⋆(M(0)) = Ω(ε^{α/(2α−1)})`. -/
theorem theorem_3 (M : Model) (hM : M.Assumption1) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∃ m ∈ Mset M ε,
      optRev M 0 + C * ε ^ (α / (2 * α - 1)) ≤ revenue M m := by sorry

end ApproxIC.LowerBound
