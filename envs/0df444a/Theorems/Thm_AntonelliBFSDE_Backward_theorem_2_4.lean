-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_theorem_2_4
-- name    : AntonelliBFSDE.Backward.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:40.243981+00:00
-- url     : https://prove2.me/theorems/49c0e0b2-cd1f-437a-abd1-9b4c456ddeae
-- title:
--   Theorem 2.4 — the backward equation (2.1) has a unique adapted càdlàg solution in $L^1(\mu)$
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t),P)$ satisfy the usual hypotheses, let $T>0$, and let $A$ be an adapted process of bounded variation with $A_0=0$, right-continuous paths and $|A|_T\le\beta$ for a constant $\beta>0$. Let $g$, $Y$, $k$ satisfy hypotheses 1–4 and let
--   $$G(V)_t=E\Big(\int_t^T g_s(V_s)\,dA_s+Y\ \Big|\ \mathcal F_t\Big).\tag{2.1}$$
--   Then:
--
--   1. **(Existence)** there is a progressively measurable process $V$ with càdlàg paths on $[0,T]$ and $V\in L^1(\mu)$ such that
--   $$E\Big(\int_0^T|G(V)_t-V_t|\,|dA_t|\Big)=0,$$
--   and $V$ is a semimartingale through the decomposition (2.9): there is a càdlàg martingale $M$ with $M_t=E\big(\int_0^T g_s(V_s)\,dA_s+Y\mid\mathcal F_t\big)$ a.s. for each $t\le T$ and, almost surely, for all $t\in[0,T]$,
--   $$V_t=M_t-\int_0^t g_s(V_s)\,dA_s ;$$
--   2. **(Uniqueness)** any two $V,V'\in L^1(\mu)$ solving (2.1) in the $L^1(\mu)$ sense coincide $\mu$-almost everywhere: $E\big(\int_0^T|V_t-V'_t|\,|dA_t|\big)=0$.
--
--   This answers, for $p=1$ and $A_t=t$, a conjecture of Duffie and Epstein (1992), and requires only integrability of the data.
--
--   **Formalization Note** "Semimartingale" is expressed through the decomposition (2.9), which is the paper's own argument: a càdlàg martingale minus a finite-variation adapted process. Mathlib's `Martingale` is indexed by all of $\mathbb R_{\ge0}$, so the martingale property is stated for the stopped process $t\mapsto M_{\min(t,T)}$. Uniqueness quantifies over all of $L^1(\mu)$, which has no adaptedness requirement, as on p. 779. A solution must have a càdlàg version of $G(V)$ with integrable arguments (see the definition of $L^1(\mu)$ solutions), which rules out junk conditional expectations. Integrals $\int_t^T$ are over $(t,T]$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 780, Theorem 2.4; (2.1) p. 778; hypotheses 1–4 p. 779; (2.9) p. 783

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Theorem 2.4 (Antonelli 1993, p. 780): under hypotheses 1–4, the backward equation (2.1)
`V_t = E(∫_t^T g_s(V_s) dA_s + Y | 𝓕_t)` has a progressively measurable càdlàg solution in the
`L¹(μ)` sense, which is a semimartingale through the decomposition (2.9)
`V_t = E(∫_0^T g_s(V_s) dA_s + Y | 𝓕_t) - ∫_0^t g_s(V_s) dA_s`, and any two `L¹(μ)` solutions
agree `μ`-almost everywhere. -/
theorem theorem_2_4 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (T β : ℝ≥0) (hT : 0 < T) (hβ : 0 < β) (I : BVIntegrator 𝓕 T β)
    (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ) (k : ℝ) (hyp : Hypotheses 𝓕 P I g Y k) :
    (∃ V : ℝ≥0 → Ω → ℝ, IsProgressive 𝓕 V ∧ (∀ ω, IsCadlagOn (fun t => V t ω) T) ∧
      IsL1Solution 𝓕 P I g Y V ∧
      ∃ M : ℝ≥0 → Ω → ℝ, Martingale (fun t => M (min t T)) 𝓕 P ∧
        (∀ ω, IsCadlagOn (fun t => M t ω) T) ∧
        (∀ t ≤ T, M t =ᵐ[P] MeasureTheory.condExp (𝓕 t) P (xi I g Y V 0)) ∧
        ∀ᵐ ω ∂P, ∀ t ≤ T, V t ω = M t ω - I.integral (fun s ω => g s ω (V s ω)) 0 t ω) ∧
    ∀ V V' : ℝ≥0 → Ω → ℝ, IsL1Solution 𝓕 P I g Y V → IsL1Solution 𝓕 P I g Y V' →
      ∫⁻ ω, I.absLIntegral (fun s ω => V s ω - V' s ω) 0 T ω ∂P = 0 := by sorry

end AntonelliBFSDE.Backward
