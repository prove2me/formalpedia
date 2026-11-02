-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_star_exists
-- name    : DelayImpulse.Optimal.theorem_6_1_star_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T23:20:28.064131+00:00
-- url     : https://prove2.me/theorems/655d1c9e-5017-430d-8354-65e4a9aaca91
-- title:
--   Theorem 6.1, p. 14 — the strategy δ* (iterated hitting times τ*ₙ with measurable maximisers β*ₙ) is well defined
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying a standard $d$-dimensional Brownian motion $B$, $(\mathcal F_t)_{t\ge0}$ is its natural filtration augmented by the $P$-null sets, and the data $(U,\Delta,r,k,\varphi,\gamma,h,L)$ satisfy the standing hypotheses of §3 and Assumption 3.1 ($U\subset\mathbb R^l$ finite and nonempty, $\Delta>0$, $r>0$, $k>0$, $\varphi\ge0$ on $U$, $L$ progressively measurable, $h$ progressively measurable in $(t,\omega)$ and $0\le h\le\gamma$ a.s.); $\psi=k+\varphi$.
--
--   Let $(Y^n,O^n)_n$ be the iterative scheme (4.4)–(4.6), $Y=\lim_n Y^n$ its limit, and $O$ the obstacle (4.14) built from $Y$. Then the strategy $\delta^*=(\tau^*_n,\beta^*_n)_{n\ge0}$ of Theorem 6.1 can be defined, i.e. there exist stopping times $\tau^*_n$ and $U$-valued $\mathcal F_{\tau^*_n}$-measurable random variables $\beta^*_n$ such that, almost surely,
--   $$\tau^*_0=\inf\{s\ge0:\ O_s(0,0)\ge Y_s(0,0)\},\qquad \tau^*_n=\inf\{s\ge\tau^*_{n-1}+\Delta:\ O_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\ge Y_s(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})\}\quad(n\ge1)$$
--   (with $\inf\emptyset=+\infty$), and, for every $n\ge0$, almost surely
--   $$O_{\tau^*_n}(\mathrm{prev}_n)=\mathbb E\Big[\int_{\tau^*_n}^{\tau^*_n+\Delta}e^{-rs}h(s,L_s+\beta^*_0+\dots+\beta^*_{n-1})\,ds-e^{-r(\tau^*_n+\Delta)}\psi(\beta^*_n)+Y_{\tau^*_n+\Delta}(\tau^*_n,\beta^*_0+\dots+\beta^*_n)\,\Big|\,\mathcal F_{\tau^*_n}\Big],$$
--   where $\mathrm{prev}_0=(0,0)$ and $\mathrm{prev}_n=(\tau^*_{n-1},\beta^*_0+\dots+\beta^*_{n-1})$ for $n\ge1$.
--
--   This is the well-posedness of the sentence "let us define the strategy $\delta^*$" in Theorem 6.1: the hitting times are stopping times (up to a null set) and a measurable maximiser $\beta^*_n$ exists, constructed as in the proof of Proposition 5.3, (5.17)–(5.18). Together with the two parts of the proof of Theorem 6.1 it yields the optimality of $\delta^*$.
--
--   **Formalization Note** The statement is `∃ δ, IsStarStrategy 𝓕 P D (Ylim Yn) O δ` for every scheme `(Yn, On)` (`IsScheme`) and every limit obstacle `O` (`IsLimitObstacle`), with the conventions of the definition file `DelayImpulse_Optimal_Scheme`: a process at time $+\infty$ is $0$, $e^{-r\cdot(+\infty)}=0$, $Y=\sup_nY^n$ pointwise, and each $\tau^*_n$ is a stopping time equal $P$-a.s. to the hitting time (Lean's σ-algebras are not complete). The decision index $0$ is the paper's $(\tau^*_0,\beta^*_0)$.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 14, Theorem 6.1 (definition of δ*); construction of the maximiser as in the proof of Proposition 5.3, (5.17)–(5.18), p. 8

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DelayImpulse.Optimal

theorem theorem_6_1_star_exists
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (O : Fam Ω l) (hO : IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O) :
    ∃ δ : Strategy Ω l, IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ := by sorry
end DelayImpulse.Optimal
