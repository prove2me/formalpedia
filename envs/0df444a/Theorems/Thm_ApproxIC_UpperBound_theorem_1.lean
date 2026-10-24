-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_theorem_1
-- name    : ApproxIC.UpperBound.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:44.703281+00:00
-- url     : https://prove2.me/theorems/403788d9-6b60-4959-8a8b-60d4166f343e
-- title:
--   Theorem 1, p. 16 — under local α-power envelopes, Π⋆(M(ε)) − Π⋆(M(0)) = Õ(ε^{α/(2α−1)})
-- statement:
--   Let the buyer's value have density $f$ on $S=[0,\bar v]$ satisfying Assumption 1 (a probability density with bounded variation). Suppose the revenue function $R(v)=v\bar F(v)$ admits local $\alpha$-power envelopes (Definition 1) at its unique interior maximizer $p^\star$, with constants $\alpha>1$, $\kappa_L,\kappa_U>0$ on the neighborhood $\mathcal N_\ell=(p^\star-\ell,p^\star+\ell)$, and that
--   $$\inf_{p\in S\setminus\mathcal N_\ell}|\dot R(p)|>0,\qquad \dot R(p)=\bar F(p)-pf(p).$$
--   Then
--   $$\Pi^\star(\mathcal M(\varepsilon))-\Pi^\star(\mathcal M(0))=\tilde O\big(\varepsilon^{\alpha/(2\alpha-1)}\big),$$
--   that is, there are $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ and every $\varepsilon$-incentive-compatible, individually rational mechanism $m$,
--   $$\Pi(m)-\Pi^\star(\mathcal M(0))\le C\,\varepsilon^{\alpha/(2\alpha-1)}\log(1/\varepsilon).$$
--
--   Relaxing incentive compatibility by $\varepsilon$ raises the optimal revenue by at most $\varepsilon^{\alpha/(2\alpha-1)}$ up to a logarithmic factor; the exponent is governed by the curvature of $R$ at the optimal posted price. Since $\alpha/(2\alpha-1)>1/2$, this improves the $O(\varepsilon^{1/2})$ bound of Proposition 1 for such distributions.
--
--   **Formalization Note** "$\inf_{p\notin\mathcal N_\ell}|\dot R(p)|>0$" is read over $p\in S\setminus\mathcal N_\ell$ (off $S$, $\dot R=0$ above $\bar v$, so the unrestricted reading could never hold); as $S\setminus\mathcal N_\ell\ni 0$ is nonempty, it is equivalent to the existence of $\eta>0$ with $\eta\le|\dot R(p)|$ there. $\dot R$ is defined as $\bar F-vf$, which equals $R'$ wherever $f$ is continuous. The constants of Definition 1 are parameters of the theorem; $C$ and $\varepsilon_0$ come after them and before $\varepsilon$ (the paper's $\tilde O$, p. 13, including the factor $\log(1/\varepsilon)$). The difference of suprema is stated as a bound on $\Pi(m)-\Pi^\star(\mathcal M(0))$ for every $m\in\mathcal M(\varepsilon)$, which is equivalent because the revenue image of $\mathcal M(\varepsilon)$ is nonempty and bounded above by $\bar v$. $\Pi^\star(\mathcal M(0))$ stays a supremum. Mechanisms are measurable.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 16, Theorem 1 (proof pp. 45–52)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting

namespace ApproxIC.UpperBound

theorem theorem_1 (M : Model) (hM : M.Assumption1) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ)
    (hinf : ∃ η > 0, ∀ p ∈ Set.Icc 0 M.vbar \ Set.Ioo (pstar - ℓ) (pstar + ℓ), η ≤ |Rdot M p|) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∀ m ∈ Mset M ε,
      revenue M m - optRev M 0 ≤ C * ε ^ (α / (2 * α - 1)) * Real.log (1 / ε) := by sorry

end ApproxIC.UpperBound
