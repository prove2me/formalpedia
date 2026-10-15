-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_proposition_4
-- name    : ApproxIC.LowerBound.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:16.434997+00:00
-- url     : https://prove2.me/theorems/0b768bab-87d4-4d08-bcff-ee7778247678
-- title:
--   Proposition 4, p. 33 — (ODE)-(DDE) has a unique solution on [0, p⋆+δ]; it is positive, non-decreasing and given by eq. (25)
-- statement:
--   Let $\varepsilon>0$, $\mu>0$ and $0<\delta<p^\star$ with $\mu\le p^\star-\delta$. Then:
--   1. the system (ODE)-(DDE) of Proposition 3 has a solution;
--   2. any two solutions agree on $[0,p^\star+\delta]$;
--   3. every solution $x$ is strictly positive and non-decreasing on $[0,p^\star+\delta]$, and admits the closed form of eq. (25):
--   $$x(v)=\frac{\varepsilon}{\mu}\exp\!\Big(\frac{v-p^\star+\delta+\mu}{\mu}\Big)\,y_{pd}(v),\qquad v\in[0,p^\star+\delta],$$
--   where $y_{pd}(v)=\frac{\mu}{p^\star-\delta-v}e^{-(v-p^\star+\delta+\mu)/\mu}$ for $v\le p^\star-\delta-\mu$, $y_{pd}(v)=1$ on $[p^\star-\delta-\mu,p^\star-\delta]$, and
--   $$y_{pd}(v)=\sum_{j=0}^{\lfloor (v-p^\star+\delta)/\mu\rfloor+1}\frac{(-1)^je^{-j}}{j!}\Big(\frac{v-p^\star+\delta}{\mu}+1-j\Big)^j\quad\text{on }[p^\star-\delta,p^\star+\delta].$$
--
--   So the perturbed delayed mechanism is well defined and explicitly computable.
--
--   **Formalization Note** "Unique" is uniqueness on $[0,p^\star+\delta]$, the domain of the system. "Admits a closed-form representation" is made precise by the closed form the proof gives (eq. (25), pp. 55–56, via the change of variables $y_{pd}(v)=x_{pd}(v)\frac{\mu}{\varepsilon}e^{-(v-p^\star+\delta+\mu)/\mu}$). The price $p^\star$ is a free real; $\mu\le p^\star-\delta$ is a disclosed addition presumed by the definition of $w$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 33, Proposition 4; pp. 55–56, proof of Proposition 4, eq. (25)

import Mathlib
import Definitions.Def_ApproxIC_LowerBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

/-- Proposition 4 (p. 33), with the closed form of eq. (25) (pp. 55–56): the system (ODE)-(DDE)
has a solution on `[0, p⋆ + δ]`, unique there; every solution is strictly positive and
non-decreasing on `[0, p⋆ + δ]` and equals `(ε/μ) · exp((v − p⋆ + δ + μ)/μ) · y_pd(v)` there. -/
theorem proposition_4 (pstar μ δ ε : ℝ) (hε : 0 < ε) (hμ : 0 < μ) (hδ : 0 < δ)
    (hδp : δ < pstar) (hμp : μ ≤ pstar - δ) :
    (∃ x, IsPDSolution pstar μ δ ε x) ∧
    (∀ x y, IsPDSolution pstar μ δ ε x → IsPDSolution pstar μ δ ε y →
      Set.EqOn x y (Set.Icc 0 (pstar + δ))) ∧
    (∀ x, IsPDSolution pstar μ δ ε x →
      (∀ v ∈ Set.Icc 0 (pstar + δ), 0 < x v) ∧ MonotoneOn x (Set.Icc 0 (pstar + δ)) ∧
      ∀ v ∈ Set.Icc 0 (pstar + δ),
        x v = ε / μ * Real.exp ((v - pstar + δ + μ) / μ) * yPD pstar μ δ v) := by sorry

end ApproxIC.LowerBound
