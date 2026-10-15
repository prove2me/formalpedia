-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_delta_bound_below
-- name    : ApproxIC.UpperBound.delta_bound_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:10.407988+00:00
-- url     : https://prove2.me/theorems/37115f6e-882d-4c97-9fdf-e1822cc2bfc5
-- title:
--   Appendix A, proof of Theorem 1, pp. 51–52 — ∆(v) ≤ −Ṙ(v) + C·ε^β a.e. on [0, p⋆]
-- statement:
--   Assume Assumption 1, let $p^\star\in(0,\bar v)$ maximize $R$ on $[0,\bar v]$, let $\beta\in(0,1/2)$, and let $\Delta$ be the dual virtual value of the path of eq. (9) with Lemma 2's dual solution. There are constants $C>0$ and $\varepsilon_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0]$,
--   $$\Delta(v)\le-\dot R(v)+C\,\varepsilon^\beta\qquad\text{for almost every }v\in[0,p^\star],$$
--   where $-\dot R(v)=vf(v)-\bar F(v)$.
--
--   Below $p^\star$ this bounds $\Phi_2$'s integrand by a quantity that is negative except within $O(\varepsilon^{\beta/(\alpha-1)})$ of $p^\star$, which controls the part of $\Phi_2$ below the optimal price in the proof of Theorem 1.
--
--   **Formalization Note** This is an unnumbered conclusion in the proof of Theorem 1 (Appendix A, pp. 51–52). $\dot R$ is $\bar F(v)-vf(v)$, not a derivative. $C,\varepsilon_0$ are chosen after the distribution, $p^\star$ and $\beta$, and before $\varepsilon$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), Appendix A, proof of Theorem 1, pp. 51–52, Case 2 conclusion (derivation pp. 49–51)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Eq9

namespace ApproxIC.UpperBound

open MeasureTheory

theorem delta_bound_below (M : Model) (hM : M.Assumption1) (pstar : ℝ)
    (hp : pstar ∈ Set.Ioo 0 M.vbar) (hmax : IsMaxOn (R M) (Set.Icc 0 M.vbar) pstar)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
      ∀ᵐ v ∂(volume.restrict (Set.Icc 0 pstar)),
        DeltaEq9 M pstar β ε v ≤ -Rdot M v + C * ε ^ β := by sorry

end ApproxIC.UpperBound
