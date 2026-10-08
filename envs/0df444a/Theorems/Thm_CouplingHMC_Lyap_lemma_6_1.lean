-- Prove2me | Theorems.Thm_CouplingHMC_Lyap_lemma_6_1
-- name    : CouplingHMC.Lyap.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:23.373983+00:00
-- url     : https://prove2.me/theorems/fb60a12a-f089-4689-8002-4ffbb957dca2
-- title:
--   Lemma 6.1, p. 42 — a locally contractive coupling yields a coupled chain whose stopped process e^{c(n∧T)}ρ(X_{n∧T},Y_{n∧T}) is a supermartingale
-- statement:
--   Let $\pi(x,dy)$ be a Markov transition kernel on a complete separable metric space $(S,\rho)$. Let $c>0$, let $A\subseteq S$ be measurable, let $(\Omega,\mathcal A,P)$ be a probability space and let $(x,y,\omega)\mapsto(X'(x,y)(\omega),Y'(x,y)(\omega))$ be a measurable map $S\times S\times\Omega\to S\times S$ such that, for all $x,y\in S$, $(X'(x,y),Y'(x,y))$ is a coupling of $\pi(x,\cdot)$ and $\pi(y,\cdot)$ and
--   $$E[\rho(X'(x,y),Y'(x,y))]\le e^{-c}\rho(x,y)\qquad\text{for }x,y\in A.\tag{130}$$
--   Then for every probability measure $\gamma$ on $S\times S$ there is a probability measure $\widetilde P$ on the path space $(S\times S)^{\mathbb N}$ under which the coordinate process $(X_n,Y_n)_{n\ge0}$ satisfies:
--
--   1. $(X_0,Y_0)\sim\gamma$;
--   2. $(X_n,Y_n)$ is a time-homogeneous Markov chain on $S\times S$ for some Markov kernel;
--   3. both $(X_n)$ and $(Y_n)$ are Markov chains with transition kernel $\pi$, with respect to the filtration $\mathcal F_n=\sigma((X_i,Y_i):i\le n)$ of the pair;
--   4. the process
--   $$M_n=e^{c(n\wedge T)}\rho(X_{n\wedge T},Y_{n\wedge T}),\qquad T=\min\{n\ge0:(X_n,Y_n)\notin A\times A\},\tag{131}$$
--   is a non-negative $(\mathcal F_n)$-supermartingale.
--
--   The lemma turns a one-step contraction on $A\times A$ into a pathwise exponential decay up to the exit time from $A\times A$; it is the basis of all bounds in §2.6.
--
--   **Formalization Note.** The Markov chain is realized as the coordinate process on the canonical path space, which determines it up to its law, the only thing the later proofs use. The marginal Markov property is stated with respect to the joint filtration of the pair, which implies the Markov property in each marginal's own filtration. The supermartingale property is the generalized $[0,\infty]$-valued one, $E[M_{n+1};F]\le E[M_n;F]$ for $F\in\mathcal F_n$, without integrability (the page does not assume $\int\rho\,d\gamma<\infty$). $T=\infty$ when the chain never leaves $A\times A$, and then $n\wedge T=n$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Lemma 6.1, (130)–(131), p. 42

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap

theorem lemma_6_1 {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (π : Kernel S S) [IsMarkovKernel π] (c : ℝ) (hc : 0 < c) (A : Set S) (hA : MeasurableSet A)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (XY : S × S × Ω → S × S) (hXY : Measurable XY)
    (hcoup : ∀ x y, P.map (fun ω => (XY (x, y, ω)).1) = π x ∧
      P.map (fun ω => (XY (x, y, ω)).2) = π y)
    (h130 : ∀ x ∈ A, ∀ y ∈ A,
      ∫⁻ ω, ENNReal.ofReal (dist (XY (x, y, ω)).1 (XY (x, y, ω)).2) ∂P ≤
        ENNReal.ofReal (Real.exp (-c) * dist x y))
    (γ : Measure (S × S)) [IsProbabilityMeasure γ] :
    ∃ Pt : Measure (ℕ → S × S), IsProbabilityMeasure Pt ∧
      Pt.map (fun ω => ω 0) = γ ∧
      (∃ K : Kernel (S × S) (S × S), IsMarkovKernel K ∧ IsMarkovChainLaw K Pt) ∧
      IsMarginalMarkov π Pt ∧
      IsStoppedSupermartingale A c Pt := by sorry

end CouplingHMC.Lyap
