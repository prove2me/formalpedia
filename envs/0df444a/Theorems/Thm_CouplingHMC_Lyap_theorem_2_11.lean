-- Prove2me | Theorems.Thm_CouplingHMC_Lyap_theorem_2_11
-- name    : CouplingHMC.Lyap.theorem_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:29:06.460369+00:00
-- url     : https://prove2.me/theorems/6cecd219-1836-44d8-93ed-bc2b56e16a40
-- title:
--   Theorem 2.11, pp. 18–19 — under Assumption 2.3, W_ρ(νπⁿ, ηπⁿ) ≤ e^{−cn}W_ρ(ν, η) + βⁿλⁿ⁻¹(∫ψdν + ∫ψdη)δ(C)
-- statement:
--   Let $\pi(x,dy)$ be the transition kernel of a Markov chain on a complete separable metric space $(S,\rho)$, and let $\mathcal W_\rho$ be the Kantorovich distance on probability measures on $S$:
--   $$\mathcal W_\rho(\nu,\eta)=\inf_{\gamma\in C(\nu,\eta)}\int\rho(x,y)\,\gamma(dx\,dy).$$
--   Suppose Assumption 2.3 holds with a constant $C\in(0,\infty)$ and measurable functions $\psi,\varphi:S\to(0,\infty)$:
--
--   1. (C1) there is $\lambda\in[1,\infty)$ with $(\pi\psi)(x)\le\lambda\psi(x)$ for all $x$ with $\psi(x)\le C$;
--   2. (C2) there is $\beta\in[1,\infty)$ with $(\pi\varphi)(x)\le\beta\varphi(x)$ and $\rho(x,y)\le\varphi(x)+\varphi(y)$ for all $x,y$;
--   3. (C3) there are a probability space $(\Omega,\mathcal A,P)$, a constant $c\in(0,\infty)$ and a measurable map $(X',Y'):S\times S\times\Omega\to S\times S$ such that for all $x,y$, $(X'(x,y,\cdot),Y'(x,y,\cdot))$ is a coupling of $\pi(x,\cdot)$ and $\pi(y,\cdot)$ with $E[\rho(X'(x,y,\cdot),Y'(x,y,\cdot))]\le e^{-c}\rho(x,y)$ whenever $\psi(x)\le C$ and $\psi(y)\le C$.
--
--   Then for every $n\in\mathbb N$ and all probability measures $\nu,\eta$ on $(S,\mathcal B(S))$,
--   $$\mathcal W_\rho(\nu\pi^n,\eta\pi^n)\le e^{-cn}\mathcal W_\rho(\nu,\eta)+\beta^n\lambda^{n-1}\Big(\int\psi\,d\nu+\int\psi\,d\eta\Big)\delta(C),\tag{42}$$
--   where
--   $$\delta(C)=\sup\Big\{\frac{\varphi(x)+\varphi(y)}{\psi(x)+\psi(y)}:x,y\in S,\ \psi(x)>C\text{ or }\psi(y)>C\Big\}.\tag{43}$$
--
--   The theorem converts contractivity of a coupling on a sublevel set of a Lyapunov function into a global bound on the distance between the laws after $n$ steps; the second term is made small by choosing $C$ large. In the paper it is applied to numerical Hamiltonian Monte Carlo, whose contraction is only established on a ball.
--
--   **Formalization Note.** $\mathcal W_\rho$, $\delta(C)$ and the integrals of $\psi$ take values in $[0,\infty]$ (lower Lebesgue integrals), with $0\cdot\infty=0$. The realization $(\Omega,P,(X',Y'))$ of (C3) is a parameter of the theorem, which then holds for every such realization. $\lambda^{n-1}$ is an integer power, so $n=0$ gives $\lambda^{-1}$ and (42) is trivially true. $\nu\pi^n$ is the bind of $\nu$ with the $n$-fold composition of $\pi$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Theorem 2.11, Assumption 2.3, (42)–(43), pp. 18–19

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap

theorem theorem_2_11 {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (π : Kernel S S) [IsMarkovKernel π] (ψ φ : S → ℝ) (hψm : Measurable ψ) (hφm : Measurable φ)
    (hψ : ∀ x, 0 < ψ x) (hφ : ∀ x, 0 < φ x) (C : ℝ) (hC : 0 < C) (lam β c : ℝ)
    (hC1 : MainLyapunov π ψ C lam) (hC2 : GlobalLyapunov π φ β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (XY : S × S × Ω → S × S)
    (hC3 : LocalContractivity π ψ C P XY c)
    (n : ℕ) (ν η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    kantorovich (ν.bind (iterKernel π n)) (η.bind (iterKernel π n)) ≤
      ENNReal.ofReal (Real.exp (-(c * n))) * kantorovich ν η +
        ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) *
          ((∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (ψ x) ∂η) * deltaC ψ φ C := by sorry

end CouplingHMC.Lyap
