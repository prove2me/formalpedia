-- Prove2me | Theorems.Thm_Avram2004_Canadized_h_integral_form
-- name    : Avram2004.Canadized.h_integral_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:50:41.073985+00:00
-- url     : https://prove2.me/theorems/48e1652e-00a1-4da5-9c33-f73e4bdbcc05
-- title:
--   §7, proof of Theorem 3 — h(z) = e^z + (p − λ)e^z ∫_0^{κ_*−z} W^(p)(y)dy ≥ e^z
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. $W^{(p)}$ and $Z^{(p)}(x)=1+p\int_{-\infty}^xW^{(p)}(y)\,dy$ are the scale functions of $(X,\mathbb P)$. Let $\kappa_*$ and $h$ be as in Theorem 3. Then for every $z\ge0$
--   $$
--   h(z)=e^z+(p-\lambda)e^z\int_0^{\kappa_*-z}W^{(p)}(y)\,dy\ \ge\ e^z.
--   $$
--
--   The inequality says that the candidate value dominates the immediate-exercise payoff $e^z$, which is needed to conclude optimality from the supermartingale property of $U$.
--
--   **Formalization Note** $\int_0^{\kappa_*-z}$ is an oriented interval integral; for $z>\kappa_*$ it is $0$ because $W^{(p)}$ vanishes on $(-\infty,0]$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 235, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- §7, proof of Theorem 3, p. 235 (first display): for `z ≥ 0`, with `p = α + λ + r`,
`h(z) = e^z + (p - λ) e^z ∫_0^{κ_* - z} W^{(p)}(y) dy ≥ e^z`. -/
theorem h_integral_form {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (z : ℝ) (hz : 0 ≤ z) :
    hCR P X p lam z =
        Real.exp z + (p - lam) * Real.exp z * ∫ y in (0 : ℝ)..(kappaLow P X p lam - z), Shared.W P X 0 p y ∧
      Real.exp z ≤ hCR P X p lam z := by sorry

end Avram2004.Canadized
