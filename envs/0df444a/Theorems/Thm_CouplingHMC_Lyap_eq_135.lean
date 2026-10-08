-- Prove2me | Theorems.Thm_CouplingHMC_Lyap_eq_135
-- name    : CouplingHMC.Lyap.eq_135
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:35.177778+00:00
-- url     : https://prove2.me/theorems/c24c8198-31be-402c-b1a2-5fe8c98eb156
-- title:
--   (135), proof of Theorem 2.11, pp. 43–44 — E[ρ(X_n,Y_n); n > T] ≤ βⁿE[ψ(X_T)+ψ(Y_T); n > T]δ(C) via (C2)
-- statement:
--   Let $\pi$ be a Markov kernel on a complete separable metric space $(S,\rho)$, let $\psi,\varphi:S\to(0,\infty)$ be measurable, $C\in\mathbb R$, and suppose (C2) holds: $\beta\ge1$, $(\pi\varphi)(x)\le\beta\varphi(x)$ and $\rho(x,y)\le\varphi(x)+\varphi(y)$ for all $x,y$. Let $\widetilde P$ be a probability measure on $(S\times S)^{\mathbb N}$ under which both coordinate processes $(X_n)$ and $(Y_n)$ are Markov chains with kernel $\pi$ with respect to the joint filtration $\mathcal F_n=\sigma((X_i,Y_i):i\le n)$. Let $T=\min\{n\ge0:\psi(X_n)>C\text{ or }\psi(Y_n)>C\}$ and let $\delta(C)$ be as in (43). Then for every $n\in\mathbb N$,
--   $$\begin{aligned}E[\rho(X_n,Y_n);\,n>T]&\le E[\varphi(X_n)+\varphi(Y_n);\,n>T]\\&\le\beta^nE[\varphi(X_T)+\varphi(Y_T);\,n>T]\\&\le\beta^nE[\psi(X_T)+\psi(Y_T);\,n>T]\,\delta(C).\end{aligned}$$
--
--   This bounds the contribution of the paths that have left $\{\psi\le C\}^2$ before time $n$ in terms of the Lyapunov function $\psi$ at the exit time.
--
--   **Formalization Note.** All expectations are lower Lebesgue integrals over the event $\{T<n\}$ in $[0,\infty]$; on that event $X_T$ is $X_{n\wedge T}$. $\delta(C)$ may be $+\infty$, with $0\cdot\infty=0$. The page's text says "the complement $\{n<T\}$" where the displays use $\{n>T\}$; the latter is formalized.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, proof of Theorem 2.11, (135) and the display following it, pp. 43–44

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap

theorem eq_135 {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (π : Kernel S S) [IsMarkovKernel π] (ψ φ : S → ℝ) (hψm : Measurable ψ) (hφm : Measurable φ)
    (hψ : ∀ x, 0 < ψ x) (hφ : ∀ x, 0 < φ x) (C β : ℝ) (hC2 : GlobalLyapunov π φ β)
    (Pt : Measure (ℕ → S × S)) [IsProbabilityMeasure Pt] (hMk : IsMarginalMarkov π Pt)
    (n : ℕ) :
    let A := {x | ψ x ≤ C}
    let E := {ω : ℕ → S × S | exitTime A ω < (n : ℕ∞)}
    ∫⁻ ω in E, ENNReal.ofReal (dist (ω n).1 (ω n).2) ∂Pt ≤
        ∫⁻ ω in E, ENNReal.ofReal (φ (ω n).1 + φ (ω n).2) ∂Pt ∧
      ∫⁻ ω in E, ENNReal.ofReal (φ (ω n).1 + φ (ω n).2) ∂Pt ≤
        ENNReal.ofReal (β ^ n) * ∫⁻ ω in E,
          ENNReal.ofReal (φ (ω (stopIdx A ω n)).1 + φ (ω (stopIdx A ω n)).2) ∂Pt ∧
      ENNReal.ofReal (β ^ n) * ∫⁻ ω in E,
          ENNReal.ofReal (φ (ω (stopIdx A ω n)).1 + φ (ω (stopIdx A ω n)).2) ∂Pt ≤
        ENNReal.ofReal (β ^ n) * (∫⁻ ω in E,
          ENNReal.ofReal (ψ (ω (stopIdx A ω n)).1 + ψ (ω (stopIdx A ω n)).2) ∂Pt) *
            deltaC ψ φ C := by sorry

end CouplingHMC.Lyap
