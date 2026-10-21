-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_proposition_6_4
-- name    : DelayImpulse.Optimal.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:53.947693+00:00
-- url     : https://prove2.me/theorems/11218caa-a192-422d-840e-f9ad0a8bc799
-- title:
--   Proposition 6.4, p. 11 — the limit value process Y(ν, ξ) of (4.13) is continuous
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)). For every index $(\nu,\xi)$, almost every path
--   $$t\mapsto Y_t(\nu,\xi)$$
--   is continuous on $[0,\infty)$.
--
--   Continuity of the value process is the main technical point of the paper: it makes the first time $Y$ meets its obstacle an optimal stopping time, from which the optimal strategy is built.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. The filtration is the augmented Brownian filtration, not an arbitrary one; the continuity relies on it.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 11, Proposition 6.4; proof pp. 11–13

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem proposition_6_4
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ) :
    ∀ᵐ ω ∂P, Continuous (fun t => Ylim Yn ν ξ t ω) := by sorry
end DelayImpulse.Optimal
