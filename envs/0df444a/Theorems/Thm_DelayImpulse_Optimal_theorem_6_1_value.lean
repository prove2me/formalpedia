-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_value
-- name    : DelayImpulse.Optimal.theorem_6_1_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:09.44493+00:00
-- url     : https://prove2.me/theorems/c57db178-ddea-4285-ae32-203884b5c05b
-- title:
--   Proof of Theorem 6.1, first part, pp. 14–15 — Y₀(0, 0) = J(δ*) for every strategy δ* built from Y and O
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.). $(Y^n,O^n)_n$ is any solution of the iterative scheme (4.4)–(4.6) and $Y=\lim_n Y^n$ (Proposition 4.2 i)), $O$ is a limit obstacle for $Y$, and $\delta^*=(\tau^*_n,\beta^*_n)_{n\ge0}$ is any strategy satisfying the defining recursion of Theorem 6.1 for $Y$ and $O$. Then, almost surely,
--   $$Y_0(0,0)=J(\delta^*).$$
--
--   This is the attainment half of Theorem 6.1: the strategy that stops at the first time the obstacle meets the value and picks the maximising impulse collects exactly the value.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. $Y_0(0,0)$ is an $\mathcal F_0$-measurable random variable, and the identity is stated $P$-a.s. The hitting times are taken up to a $P$-null set: Lean's $\sigma$-algebras are not complete, so the hitting time itself is only a stopping time for the completed filtration, and the statement uses a stopping time equal to it almost surely (which changes no expectation).
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, pp. 14–15, proof of Theorem 6.1, first part (from "We first prove that Y0(0, 0) = J(δ∗)" to "Y0(0, 0) = J(δ∗)")

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem theorem_6_1_value
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (O : Fam Ω l) (hO : IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O)
    (δ : Strategy Ω l) (hδ : IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ) :
    ∀ᵐ ω ∂P, Ylim Yn (fun _ => 0) (fun _ => 0) 0 ω = J P D δ := by sorry
end DelayImpulse.Optimal
