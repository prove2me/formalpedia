-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_proposition_A_1_5
-- name    : CarbonFBSDE.MultiPeriod.proposition_A_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:35.50812+00:00
-- url     : https://prove2.me/theorems/9f7268d8-426f-4097-b903-0e114dd2b3e4
-- title:
--   Proposition A.1 (5) (constant depending on the coefficients), p. 36 — tail bounds (A.2) of v away from the level Λ
-- statement:
--   Let Assumption 1 hold, $r\in\mathbb R$ and $\tau>0$. Given $\xi>0$ and $a\ge1$, there is a constant $C>0$ such that for every $\varphi\in\mathcal K$, with $v$ the value function of Proposition 3.2 for $\varphi$, for all $t\in[0,\tau)$, all $e,\Lambda\in\mathbb R$, every $p\in\mathbb R^d$ with $|p|\le\xi$, and $P=P^{t,p}$ the forward component of the solution started at $(t,p,e)$:
--   $$e>\Lambda\ \Longrightarrow\ v(t,p,e)\ge e^{-r(\tau-t)}\Big(\mathbb E\big[\varphi(P_\tau,\Lambda)\big]-C\Big(\frac{e-\Lambda}{L(\tau-t)}\Big)^{-a}\Big),$$
--   $$e<\Lambda\ \Longrightarrow\ v(t,p,e)\le e^{-r(\tau-t)}\Big(\mathbb E\big[\varphi(P_\tau,\Lambda)\big]+C\Big(\frac{\Lambda-e}{L(\tau-t)}\Big)^{-a}\Big).$$
--
--   These bounds say that far below (above) a level $\Lambda$ the price is at most (at least) the discounted expected terminal payoff evaluated at $\Lambda$, up to a polynomially small error. Lemma 3.13 uses them to show that the diagonal value tends to $0$ as $e\to-\infty$.
--
--   **Formalization Note** This is a **corrected** reading. The page says that $C$ depends "only on $a$, $\xi$, $L$ and $\tau$". Assumption 1 bounds no coefficient value, and that uniformity fails: with $\mu(p,y)=M-y$ and $\varphi(p,e)=\min(\max(e-\Lambda-1,0),1)$ one has $\mathbb E[\varphi(P,\Lambda)]=0$ while $v(t,p,e)\to e^{-r(\tau-t)}$ as $M\to\infty$ for fixed $e<\Lambda$. Here $C$ is chosen after the coefficients (and $\xi$, $a$), but before $\varphi$ and $L_\varphi$: the page's independence of $\varphi$ is kept, and $C$ is uniform over $\varphi\in\mathcal K$, which is how the proof of Lemma 3.13, (3.53), uses it. The page's $P^{t,p}_T$ is read as $P^{t,p}_\tau$, and a stray "$|$" inside the first expectation is dropped (typos). The expectation is of the bounded continuous function $\varphi(\cdot,\Lambda)$ of the measurable $P_\tau$.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 36, Proposition A.1 (5), (A.2)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

theorem proposition_A_1_5 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (τ : ℝ≥0) (hτ : 0 < τ) (ξ a : ℝ) (hξ : 0 < ξ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : SDEState d → ℝ → ℝ) (Lφ : ℝ), InK φ Lφ →
      ∀ v : ℝ≥0 → SDEState d → ℝ → ℝ, IsValueFn₀ B c r φ τ v →
      ∀ t < τ, ∀ (e Λ : ℝ) (p : SDEState d), ‖p‖ ≤ ξ → ∀ P E Y Z,
        IsOnePeriodSol B c r φ t τ p e P E Y Z →
        (Λ < e → Real.exp (-(r * ((τ : ℝ) - t))) *
            ((∫ ω, φ (P τ ω) Λ ∂B.Pr) - C * ((e - Λ) / (L * ((τ : ℝ) - t))) ^ (-a))
              ≤ v t p e) ∧
        (e < Λ → v t p e ≤ Real.exp (-(r * ((τ : ℝ) - t))) *
            ((∫ ω, φ (P τ ω) Λ ∂B.Pr) + C * ((Λ - e) / (L * ((τ : ℝ) - t))) ^ (-a))) := by sorry

end CarbonFBSDE.MultiPeriod
