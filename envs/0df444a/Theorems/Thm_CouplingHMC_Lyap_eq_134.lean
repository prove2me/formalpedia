-- Prove2me | Theorems.Thm_CouplingHMC_Lyap_eq_134
-- name    : CouplingHMC.Lyap.eq_134
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:29:03.62881+00:00
-- url     : https://prove2.me/theorems/3b097be0-67e0-46de-ac82-9394344e2166
-- title:
--   (134), proof of Theorem 2.11, p. 43 — e^{cn}E[ρ(X_n,Y_n); n ≤ T] ≤ E[M_n] ≤ ∫ρ dγ
-- statement:
--   Let $(S,\rho)$ be a complete separable metric space, $\psi:S\to\mathbb R$ measurable, $C\in\mathbb R$, $c>0$, and $A=\{\psi\le C\}$. Let $\widetilde P$ be a probability measure on the path space $(S\times S)^{\mathbb N}$ with coordinate process $(X_n,Y_n)$, natural filtration $(\mathcal F_n)$ and initial law $(X_0,Y_0)\sim\gamma$. Let $T=\min\{n\ge0:(X_n,Y_n)\notin A\times A\}$ (possibly $\infty$) and suppose that
--   $$M_n=e^{c(n\wedge T)}\rho(X_{n\wedge T},Y_{n\wedge T})$$
--   is a non-negative $(\mathcal F_n)$-supermartingale. Then for every $n\in\mathbb N$,
--   $$e^{cn}E[\rho(X_n,Y_n);\,n\le T]\ \le\ E\big[e^{c(n\wedge T)}\rho(X_{n\wedge T},Y_{n\wedge T})\big]\ \le\ E[\rho(X_0,Y_0)]=\int\rho\,d\gamma.$$
--
--   This is the bound on the event that the coupled chain has not yet left $\{\psi\le C\}^2$ by time $n$, the first of the three estimates combined in the proof of Theorem 2.11.
--
--   **Formalization Note.** Expectations are lower Lebesgue integrals in $[0,\infty]$; the supermartingale property is the generalized one ($E[M_{n+1};F]\le E[M_n;F]$ for $F\in\mathcal F_n$), so $\int\rho\,d\gamma=\infty$ is allowed. The page applies Lemma 6.1 "with $A=\{\psi>C\}$"; the set on which (C3) contracts and from which $T$ is the exit time is $\{\psi\le C\}$, which is used here.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, proof of Theorem 2.11, (134), p. 43

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap

theorem eq_134 {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (ψ : S → ℝ) (hψm : Measurable ψ) (C c : ℝ) (hc : 0 < c)
    (Pt : Measure (ℕ → S × S)) [IsProbabilityMeasure Pt] (γ : Measure (S × S))
    (h0 : Pt.map (fun ω => ω 0) = γ)
    (hM : IsStoppedSupermartingale {x | ψ x ≤ C} c Pt) (n : ℕ) :
    ENNReal.ofReal (Real.exp (c * n)) *
        ∫⁻ ω in {ω | (n : ℕ∞) ≤ exitTime {x | ψ x ≤ C} ω},
          ENNReal.ofReal (dist (ω n).1 (ω n).2) ∂Pt ≤
      ∫⁻ ω, ENNReal.ofReal (stoppedM {x | ψ x ≤ C} c ω n) ∂Pt ∧
    ∫⁻ ω, ENNReal.ofReal (stoppedM {x | ψ x ≤ C} c ω n) ∂Pt ≤
      ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ := by sorry

end CouplingHMC.Lyap
