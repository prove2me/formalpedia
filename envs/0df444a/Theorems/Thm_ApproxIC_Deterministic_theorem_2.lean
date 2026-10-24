-- Prove2me | Theorems.Thm_ApproxIC_Deterministic_theorem_2
-- name    : ApproxIC.Deterministic.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:24.305828+00:00
-- url     : https://prove2.me/theorems/98082917-453e-46a1-b41f-055eeeef088d
-- title:
--   Theorem 2, pp. 24–25 — optimal deterministic ε-IC mechanisms are hard/soft floors with s = p + ε, and Π⋆(M_d(ε)) − Π⋆(M(0)) = Θ(ε)
-- statement:
--   Let the buyer's value distribution satisfy Assumption 1: a density $f$ of bounded variation supported in $S=[0,\bar v]$. For $\varepsilon\ge0$ let $\mathcal M_d(\varepsilon)$ be the deterministic mechanisms ($x(v)\in\{0,1\}$) that are individually rational and $\varepsilon$-incentive compatible, let $\Pi(m)$ be the expected payment, and let $m_d(p,s)$ be the hard/soft floor mechanism
--   $$x_d(v)=\mathbf 1\{v\in[p,\bar v]\},\qquad t_d(v)=v\,\mathbf 1\{v\in[p,s)\}+s\,\mathbf 1\{v\in[s,\bar v]\}.$$
--
--   1. **(Optimal deterministic mechanism.)** For every $\varepsilon>0$ there is a hard floor $p\in[0,\bar v]$ such that $m_d(p,p+\varepsilon)\in\mathcal M_d(\varepsilon)$, no mechanism of $\mathcal M_d(\varepsilon)$ earns more than $m_d(p,p+\varepsilon)$, and $p$ maximizes $p'\mapsto\Pi(m_d(p',p'+\varepsilon))$ over $[0,\bar v]$.
--   2. **(Linear gains.)** $\Pi^\star(\mathcal M_d(\varepsilon))-\Pi^\star(\mathcal M(0))=\Theta(\varepsilon)$: there are constants $c>0$, $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$
--   $$\Pi^\star(\mathcal M(0))+c\,\varepsilon\;\le\;\Pi^\star(\mathcal M_d(\varepsilon))\;\le\;\Pi^\star(\mathcal M(0))+C\,\varepsilon .$$
--
--   The theorem shows that with deterministic mechanisms the seller cannot turn the relaxation of the incentive constraints into more than a linear gain in $\varepsilon$, and that a linear gain is always achievable; the paper's other results show that randomized mechanisms do strictly better.
--
--   **Formalization Note** "Θ" is read as $\mathcal O$ and $\Omega$ together, per the paper's notation (p. 13); the constants $c, C, \varepsilon_0$ depend on the distribution but not on $\varepsilon$. The $\Theta(\varepsilon)$ claim is stated in the equivalent form "some $m\in\mathcal M_d(\varepsilon)$ earns at least $\Pi^\star(\mathcal M(0))+c\varepsilon$, and every $m\in\mathcal M_d(\varepsilon)$ earns at most $\Pi^\star(\mathcal M(0))+C\varepsilon$", which equals the supremum form because the revenue image of $\mathcal M_d(\varepsilon)$ is nonempty and bounded above; $\Pi^\star(\mathcal M(0))$ is kept as a supremum. The payment region $[p,s)$ follows the proof (p. 52); the theorem's display prints $[p,s]$, which counts $2s$ at $v=s$. The hard floor ranges over $[0,\bar v]$; when $p+\varepsilon>\bar v$ the soft floor lies beyond the support, a harmless extension of the paper's family $p\le s\le\bar v$ (on $S$ such a mechanism coincides with $m_d(p,\bar v)$). Mechanisms are measurable (disclosed convention of the setting).
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), pp. 24–25, Theorem 2; proof in Appendix B, pp. 52–53

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

namespace ApproxIC.Deterministic

theorem theorem_2 (M : Model) (hM : M.Assumption1) :
    (∀ ε > 0, ∃ p ∈ Set.Icc 0 M.vbar,
        hardSoft p (p + ε) ∈ Mdset M ε ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ revenue M (hardSoft p (p + ε))) ∧
        (∀ p' ∈ Set.Icc 0 M.vbar,
          revenue M (hardSoft p' (p' + ε)) ≤ revenue M (hardSoft p (p + ε)))) ∧
    (∃ c > 0, ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
        (∃ m ∈ Mdset M ε, optRev M 0 + c * ε ≤ revenue M m) ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ optRev M 0 + C * ε)) := by sorry

end ApproxIC.Deterministic
