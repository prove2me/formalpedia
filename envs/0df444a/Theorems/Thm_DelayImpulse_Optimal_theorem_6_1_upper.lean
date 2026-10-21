-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_upper
-- name    : DelayImpulse.Optimal.theorem_6_1_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:11.616546+00:00
-- url     : https://prove2.me/theorems/bc94613b-328c-4e87-bb25-bb467d509e31
-- title:
--   Proof of Theorem 6.1, second part, pp. 15–16 — Y₀(0, 0) ≥ J(δ′) for every admissible strategy δ′
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)). For every admissible strategy $\delta'\in\mathcal A$, almost surely,
--   $$J(\delta')\le Y_0(0,0).$$
--
--   This is the upper-bound half of Theorem 6.1: no admissible strategy earns more than the value of the scheme. With the first part it gives $J(\delta^*)\ge J(\delta')$.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, pp. 15–16, proof of Theorem 6.1, second part (from "To proceed, we prove" to "Hence, the strategy δ∗ is optimal.")

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem theorem_6_1_upper
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (δ' : Strategy Ω l) (hδ' : IsAdmissible (ReflectedBSDE.Existence.augmentedFiltration P hB) P D δ') :
    ∀ᵐ ω ∂P, J P D δ' ≤ Ylim Yn (fun _ => 0) (fun _ => 0) 0 ω := by sorry
end DelayImpulse.Optimal
