-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_eq_6_27
-- name    : DelayImpulse.Optimal.eq_6_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:47.50685+00:00
-- url     : https://prove2.me/theorems/49c465e5-8921-43bd-9768-22358b3e280f
-- title:
--   (6.27), proof of Proposition 6.4, p. 13 — |Oₜ(ν, ξ)| ≤ (γ/r){e^{−rt} − e^{−r(t+Δ)}} + ‖ψ‖e^{−r(t+Δ)} + (γ/r)e^{−r(t+Δ)}
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)), and $O$ is a limit obstacle for $Y$ (4.14). For every index $(\nu,\xi)$, almost surely, for all $t\ge0$,
--   $$|O_t(\nu,\xi)|\le\frac{\gamma}{r}\big\{e^{-rt}-e^{-r(t+\Delta)}\big\}+\|\psi\|e^{-r(t+\Delta)}+\frac{\gamma}{r}e^{-r(t+\Delta)},$$
--   where $\|\psi\|=\max_{\beta\in U}|\psi(\beta)|$.
--
--   In particular $O_t(\nu,\xi)\to0$ as $t\to\infty$ uniformly in the index, which is used in the continuity proof of Proposition 6.4.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The paper does not define $\|\psi\|$; it is read as the maximum of $|\psi|$ over the finite set $U$.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 13, (6.27) in the proof of Proposition 6.4

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem eq_6_27
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (O : Fam Ω l) (hO : IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O)
    (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, |O ν ξ t ω| ≤
      D.γ / D.r * (Real.exp (-D.r * t) - Real.exp (-D.r * ((t : ℝ) + D.Δ)))
      + psiNorm D hD.U_nonempty * Real.exp (-D.r * ((t : ℝ) + D.Δ))
      + D.γ / D.r * Real.exp (-D.r * ((t : ℝ) + D.Δ)) := by sorry
end DelayImpulse.Optimal
