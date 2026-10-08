-- Prove2me | Theorems.Thm_CouplingHMC_Lyap_eq_136
-- name    : CouplingHMC.Lyap.eq_136
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:54.18796+00:00
-- url     : https://prove2.me/theorems/198b62ad-8735-48a5-8458-01148b6ddb02
-- title:
--   (136), proof of Theorem 2.11, p. 44 — E[ψ(X_T)+ψ(Y_T); n > T] ≤ λⁿ⁻¹(∫ψ dν + ∫ψ dη) via (C1)
-- statement:
--   Let $\pi$ be a Markov kernel on a complete separable metric space $S$, let $\psi:S\to(0,\infty)$ be measurable, $C\in\mathbb R$, and suppose (C1) holds: $\lambda\ge1$ and $(\pi\psi)(x)\le\lambda\psi(x)$ whenever $\psi(x)\le C$. Let $\widetilde P$ be a probability measure on $(S\times S)^{\mathbb N}$ under which both coordinate processes $(X_n)$ and $(Y_n)$ are Markov chains with kernel $\pi$ with respect to the joint filtration of the pair, with $X_0\sim\nu$ and $Y_0\sim\eta$. Let $T=\min\{n\ge0:\psi(X_n)>C\text{ or }\psi(Y_n)>C\}$. Then for every $n\in\mathbb N$,
--   $$E[\psi(X_T)+\psi(Y_T);\,n>T]\ \le\ \lambda^{n-1}\Big(\int\psi\,d\nu+\int\psi\,d\eta\Big).$$
--
--   Together with (134) and (135) this yields the bound (42) of Theorem 2.11.
--
--   **Formalization Note.** Expectations and integrals are lower Lebesgue integrals in $[0,\infty]$; $\int\psi\,d\nu=\infty$ is allowed. $\lambda^{n-1}$ is an integer power, so at $n=0$ it is $\lambda^{-1}$, and the left side is $0$ because $\{T<0\}$ is empty.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, proof of Theorem 2.11, (136), p. 44

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap

theorem eq_136 {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (π : Kernel S S) [IsMarkovKernel π] (ψ : S → ℝ) (hψm : Measurable ψ)
    (hψ : ∀ x, 0 < ψ x) (C lam : ℝ) (hC1 : MainLyapunov π ψ C lam)
    (Pt : Measure (ℕ → S × S)) [IsProbabilityMeasure Pt] (hMk : IsMarginalMarkov π Pt)
    (ν η : Measure S) (hν : Pt.map (fun ω => (ω 0).1) = ν) (hη : Pt.map (fun ω => (ω 0).2) = η)
    (n : ℕ) :
    ∫⁻ ω in {ω | exitTime {x | ψ x ≤ C} ω < (n : ℕ∞)},
        ENNReal.ofReal (ψ (ω (stopIdx {x | ψ x ≤ C} ω n)).1 +
          ψ (ω (stopIdx {x | ψ x ≤ C} ω n)).2) ∂Pt ≤
      ENNReal.ofReal (lam ^ ((n : ℤ) - 1)) *
        ((∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (ψ x) ∂η) := by sorry

end CouplingHMC.Lyap
