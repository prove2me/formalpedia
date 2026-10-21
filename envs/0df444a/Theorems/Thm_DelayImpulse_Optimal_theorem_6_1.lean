-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_theorem_6_1
-- name    : DelayImpulse.Optimal.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:19.638045+00:00
-- url     : https://prove2.me/theorems/aa01fa2a-887c-46a6-a715-9f1e0345cd32
-- title:
--   Theorem 6.1, p. 14 — the strategy δ* built from the iterated Snell envelopes is optimal: Y₀(0,0) = sup_{δ∈𝒜} J(δ) = J(δ*)
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ measurable for $\mathcal P\otimes\mathcal B(\mathbb R^l)$ and $0\le h\le\gamma$ a.s.).
--
--   Let $(Y^n,O^n)_n$ be the iterative scheme (4.4)–(4.6), $Y=\lim_nY^n$ its limit, and $O$ the obstacle (4.14) built from $Y$. Define the strategy $\delta^*=(\tau^*_n,\beta^*_n)_{n\ge0}$ by
--   $$\tau^*_0=\inf\{s\ge0:O_s(0,0)\ge Y_s(0,0)\},\qquad\tau^*_n=\inf\{s\ge\tau^*_{n-1}+\Delta:\ O_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\ge Y_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\}$$
--   ($+\infty$ if the set is empty), with $\beta^*_n$ a $U$-valued $\mathcal F_{\tau^*_n}$-measurable maximiser:
--   $$O_{\tau^*_n}(\text{prev}_n)=\mathbb E\Big[\int_{\tau^*_n}^{\tau^*_n+\Delta}e^{-rs}h(s,L_s+\beta^*_0+\dots+\beta^*_{n-1})ds-e^{-r(\tau^*_n+\Delta)}\psi(\beta^*_n)+Y_{\tau^*_n+\Delta}(\tau^*_n,\beta^*_0+\dots+\beta^*_n)\,\Big|\,\mathcal F_{\tau^*_n}\Big],$$
--   where $\text{prev}_0=(0,0)$ and $\text{prev}_n=(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})$. Then $\delta^*$ is optimal for the impulse control problem:
--   $$Y_0(0,0)=\sup_{\delta\in\mathcal A}J(\delta)=J(\delta^*).$$
--
--   Precisely: the scheme and an obstacle $O$ exist; and for every scheme and every such $O$, a strategy $\delta^*$ as above exists, and every such $\delta^*$ is admissible, satisfies $Y_0(0,0)=J(\delta^*)$ almost surely, and $J(\delta')\le J(\delta^*)$ for every $\delta'\in\mathcal A$.
--
--   The theorem solves the infinite-horizon impulse control problem with execution delay and non-Markovian random coefficients: the value is the limit of an iterated optimal stopping scheme, and an optimal strategy is read off from the first times the value meets its obstacle.
--
--   **Formalization Note** The scheme is the predicate `IsScheme`: $Y^n$ and $O^n$ are adapted with continuous paths, $Y^0$ is given by (4.4), $O^{n}$ equals the right-hand side of (4.5) ii) a.s. at each $t$ (a pinned version of the optional projection), and $Y^{n}$ is the Snell envelope (4.6) of the reward with obstacle $O^n$; the reflected BSDE (4.5) i), iii) itself is not formalized. A process evaluated at the time $+\infty$ is $0$, and $e^{-r\cdot(+\infty)}=0$, which is the paper's convention $y_\infty=\lim_{t\to\infty}y_t$ for its processes. An index $(\nu,\xi)$ of the scheme is a stopping time $\nu$ (possibly $+\infty$) and a finitely-valued $\mathcal F_\nu$-measurable $\xi$ (p. 5). $Y=\lim_n Y^n$ is written as the pointwise supremum $\sup_n Y^n$. "$\sup_{\delta\in\mathcal A}J(\delta)=J(\delta^*)$" is stated as admissibility of $\delta^*$ plus $J(\delta')\le J(\delta^*)$ for all $\delta'\in\mathcal A$. The two existence clauses (of the scheme with its obstacle, and of $\delta^*$) are not sentences of the theorem: they express that the scheme is well-posed (Propositions 4.1, 4.2) and that "let us define the strategy $\delta^*$" is possible, and keep the universally quantified clauses from being vacuous. The paper does not say that $\beta^*_0$ is $U$-valued; it is required here, as for $n\ge1$. $Y_0(0,0)=J(\delta^*)$ is stated $P$-a.s. since $Y_0(0,0)$ is an $\mathcal F_0$-measurable random variable. The hitting times are taken up to a $P$-null set: Lean's $\sigma$-algebras are not complete, so the hitting time itself is only a stopping time for the completed filtration, and the statement uses a stopping time equal to it almost surely (which changes no expectation).
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 14, Theorem 6.1; proof pp. 14–16

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem theorem_6_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D) :
    (∃ (Yn On : ℕ → Fam Ω l) (O : Fam Ω l), IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On ∧
      IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O) ∧
    ∀ (Yn On : ℕ → Fam Ω l) (O : Fam Ω l), IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On →
      IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O →
      (∃ δ : Strategy Ω l, IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ) ∧
      ∀ δ : Strategy Ω l, IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ →
        IsAdmissible (ReflectedBSDE.Existence.augmentedFiltration P hB) P D δ ∧
        (∀ᵐ ω ∂P, Ylim Yn (fun _ => 0) (fun _ => 0) 0 ω = J P D δ) ∧
        ∀ δ' : Strategy Ω l, IsAdmissible (ReflectedBSDE.Existence.augmentedFiltration P hB) P D δ' → J P D δ' ≤ J P D δ := by sorry
end DelayImpulse.Optimal
