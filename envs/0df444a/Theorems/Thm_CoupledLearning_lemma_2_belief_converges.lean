-- Prove2me | Theorems.Thm_CoupledLearning_lemma_2_belief_converges
-- name    : CoupledLearning.lemma_2_belief_converges
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:04.505563+00:00
-- url     : https://prove2.me/theorems/78b43b56-f120-42d3-b236-4aa4af8700d8
-- title:
--   Lemma 2, p.23 — beliefs converge almost surely
-- statement:
--   Throughout, $I$ is a finite set of players, player $i$ chooses $q_i$ in a convex, closed and bounded set $Q_i\subseteq\mathbb R^{d_i}$, $Q=\prod_i Q_i$, and $S$ is a finite set of parameters with true parameter $s^*$. For each $s\in S$ and $q$, $\varphi^s(\cdot|q)$ is a probability density of payoff vectors $y\in\mathbb R^I$, continuous in $q$; $u_i^s$ is continuous on $Q$; and $F_i(\theta,q)\subseteq Q_i$ is player $i$'s set of updated strategies. The initial belief $\theta^1\in\Delta(S)$ has $\theta^1(s)>0$ for every $s$ and $q^1\in Q$. On a probability space with filtration $(\mathcal F_k)$: $q^k$ is $\mathcal F_k$-measurable, $y^k$ is $\mathcal F_{k+1}$-measurable and has conditional density $\varphi^{s^*}(\cdot|q^k)$ given $\mathcal F_k$, the belief $\theta^k$ is computed by (θ-update) at the update stages $k_1<k_2<\cdots$ (infinitely many) and is constant in between, and $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$.
--
--   Then, with probability 1, the beliefs converge to a belief:
--
--   $$\lim_{k\to\infty}\theta^k=\bar\theta\quad\text{for some }\bar\theta\in\Delta(S).$$
--
--   The limit $\bar\theta$ is random. It is the belief component of the fixed point of Theorem 1.
--
--   Differences from the source:
--   - encoding: $\varphi^s(\cdot|q)$ is a density, continuous in $q$, for $q\in Q$ → $\varphi^s(\cdot|q)$ is a density for every $q\in\prod_i\mathbb R^{d_i}$ and continuous in $q$ everywhere; reason: every instance of the paper extends (compose with the componentwise Euclidean projection onto the closed convex $Q_i$); the dynamics stays in $Q$ almost surely, so only values on $Q$ matter
--   - generalization: $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise, so $u_i^s$ is the mean payoff, continuous in $q$ → $u_i^s$ is any function continuous on $Q$, not tied to $\varphi$; reason: the proof never links $u$ to $\varphi$; taking $u_i^s$ to be the mean of $y_i$ recovers the paper's instances
--   - generalization: players update by $q_i^{k+1}\in F_i(\theta^{k+1},q^k)$ and $y^k\sim\varphi^{s^*}(\cdot|q^k)$ → $q^{k+1}$ is any adapted selection from $F(\theta^{k+1},q^k)$ (possibly randomized), and given the past $\mathcal F_k$ the payoff $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$; reason: a fixed deterministic selection rule with the natural filtration is a special case
--   - encoding: stages $k=1,2,\dots$; update stages $(k_t)$, deterministic or random, with $k_{t+1}-k_t$ finite w.p. 1 → stages indexed from $0$; a set $T(\omega)$ of update stages that contains the first stage and is infinite almost surely; reason: an index shift changes no limit; declaring the first stage an update stage gives the same beliefs as starting from $\theta^1$, and finite gaps w.p. 1 means infinitely many updates
--   - generalization: Lemma 2 is stated in the paper under its standing Assumptions 1–3 → Assumptions 1–3 are not assumed; reason: the proof does not use them; with them the statement is the paper's
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Lemma 2, p.23; proof p.40

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsModel
import Definitions.Def_CoupledLearning_IsLearningProcess
import Definitions.Def_CoupledLearning_belief

open MeasureTheory Filter Topology

namespace CoupledLearning

/-- Lemma 2, arXiv:2206.05637v2, p.23: `lim_{k→∞} θ^k = θ̄` with probability 1, where
`θ̄ ∈ Δ(S)`. Stated for every model of §2 and every realization of the learning dynamics with
`θ^1(s) > 0` for all `s` and `q^1 ∈ Q`.

**Formalization Note.** The limit `θ̄` depends on the sample point. `Δ(S)` is `stdSimplex ℝ S`.
Assumptions 1–3 are not needed (the proof, p.40, uses only Lemma 1 and (7)) and not assumed. -/
theorem lemma_2_belief_converges
    {I S : Type*} [Fintype I] [Fintype S] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (φ : S → Prof d → (I → ℝ) → ℝ) (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i))))
    (hmodel : IsModel Q φ u F)
    (sstar : S) (θ₁ : S → ℝ) (q₁ : Prof d)
    (hθ₁ : θ₁ ∈ stdSimplex ℝ S) (hθ₁_pos : ∀ s, 0 < θ₁ s) (hq₁ : q₁ ∈ Qset Q)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (q : ℕ → Ω → Prof d) (y : ℕ → Ω → (I → ℝ)) (T : Ω → Set ℕ)
    (hproc : IsLearningProcess φ F sstar θ₁ q₁ P ℱ q y T) :
    ∀ᵐ ω ∂P, ∃ θbar ∈ stdSimplex ℝ S,
      Tendsto (fun k => belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k) atTop
        (𝓝 θbar) := by sorry

end CoupledLearning
