-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_appendix_8_54
-- name    : DelayImpulse.Optimal.appendix_8_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:18.627447+00:00
-- url     : https://prove2.me/theorems/8d06b427-0c30-44d2-a57f-821e738f60ee
-- title:
--   Appendix, Part (I) iv), (8.54), p. 28 — the first time Y(ν, ξ) meets O(ν, ξ) after a stopping time θ is optimal after θ
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)), and $O$ is a limit obstacle for $Y$. Let $(\nu,\xi)$ be an index and $\theta$ a stopping time, and let
--   $$\tau^*_\theta=\inf\{s\ge\theta:\ O_s(\nu,\xi)\ge Y_s(\nu,\xi)\}\qquad(+\infty\text{ if the set is empty}).$$
--   Then there is a stopping time $\tau\ge\theta$ equal to $\tau^*_\theta$ almost surely. Writing $R_s=e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}$, the full optimal-stopping identity holds almost surely:
--   $$Y_\theta(\nu,\xi)=\mathbb E\Big[\int_\theta^{\tau}R_s\,ds+Y_\tau(\nu,\xi)\,\Big|\,\mathcal F_\theta\Big]=\mathbb E\Big[\int_\theta^{\tau}R_s\,ds+O_\tau(\nu,\xi)\,\Big|\,\mathcal F_\theta\Big]=\operatorname*{ess\,sup}_{\sigma\ge\theta}\mathbb E\Big[\int_\theta^{\sigma}R_s\,ds+O_\sigma(\nu,\xi)\,\Big|\,\mathcal F_\theta\Big].$$
--
--   This is the instance, for the Snell envelope $Y_t+\int_0^t e^{-rs}h(s,L_s+\xi)\mathbf 1_{[s\ge\nu]}ds$ of the reward $\int_0^t(\cdots)ds+O_t$, of the general fact (8.54) that the first time a continuous Snell envelope meets its reward is optimal; it is how the proof of Theorem 6.1 shows that each $\tau^*_n$ is optimal after $\tau^*_{n-1}+\Delta$.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The general statement about Snell envelopes of class [D] processes is cited, not proved, by the paper and is not formalized; only its instance for the scheme is. The hitting times are taken up to a $P$-null set: Lean's $\sigma$-algebras are not complete, so the hitting time itself is only a stopping time for the completed filtration, and the statement uses a stopping time equal to it almost surely (which changes no expectation).
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 28, Appendix Part (I) iv), (8.54); applied in the proof of Theorem 6.1, pp. 14–15

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem appendix_8_54
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (O : Fam Ω l) (hO : IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O)
    (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ)
    (θ : Ω → WithTop ℝ≥0) (hθ : IsStoppingTime (ReflectedBSDE.Existence.augmentedFiltration P hB) θ) :
    ∃ τ : Ω → WithTop ℝ≥0, IsStoppingTime (ReflectedBSDE.Existence.augmentedFiltration P hB) τ ∧
      τ =ᵐ[P] firstHit (O ν ξ) (Ylim Yn ν ξ) θ ∧ (∀ ω, θ ω ≤ τ ω) ∧
      atTime (Ylim Yn ν ξ) θ =ᵐ[P]
        P[fun ω => segInt (fun s => run D ν ξ s ω) (θ ω) (τ ω)
          + atTime (Ylim Yn ν ξ) τ ω | hθ.measurableSpace] ∧
      atTime (Ylim Yn ν ξ) θ =ᵐ[P]
        P[fun ω => segInt (fun s => run D ν ξ s ω) (θ ω) (τ ω) + atTime (O ν ξ) τ ω
          | hθ.measurableSpace] ∧
      ReflectedBSDE.Existence.IsEssSupOver P hθ.measurableSpace
        (fun σ : StopAfterTime (ReflectedBSDE.Existence.augmentedFiltration P hB) θ =>
          P[fun ω => segInt (fun s => run D ν ξ s ω) (θ ω) (σ.1 ω)
            + atTime (O ν ξ) σ.1 ω | hθ.measurableSpace])
        (atTime (Ylim Yn ν ξ) θ) := by sorry
end DelayImpulse.Optimal
