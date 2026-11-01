-- Prove2me | Theorems.Thm_CoupledLearning_lemma_3_strategy_converges
-- name    : CoupledLearning.lemma_3_strategy_converges
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:58.189956+00:00
-- url     : https://prove2.me/theorems/c2882c97-6f9b-4299-9140-7aca096899c4
-- title:
--   Lemma 3, p.23 — strategies converge almost surely to an equilibrium of $G(\bar\theta)$
-- statement:
--   Throughout, $I$ is a finite set of players, player $i$ chooses $q_i$ in a convex, closed and bounded set $Q_i\subseteq\mathbb R^{d_i}$, $Q=\prod_i Q_i$, and $S$ is a finite set of parameters with true parameter $s^*$. For each $s\in S$ and $q$, $\varphi^s(\cdot|q)$ is a probability density of payoff vectors $y\in\mathbb R^I$, continuous in $q$; $u_i^s$ is continuous on $Q$; and $F_i(\theta,q)\subseteq Q_i$ is player $i$'s set of updated strategies. The initial belief $\theta^1\in\Delta(S)$ has $\theta^1(s)>0$ for every $s$ and $q^1\in Q$. On a probability space with filtration $(\mathcal F_k)$: $q^k$ is $\mathcal F_k$-measurable, $y^k$ is $\mathcal F_{k+1}$-measurable and has conditional density $\varphi^{s^*}(\cdot|q^k)$ given $\mathcal F_k$, the belief $\theta^k$ is computed by (θ-update) at the update stages $k_1<k_2<\cdots$ (infinitely many) and is constant in between, and $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$.
--
--   Assume Assumptions 1–3. Then, with probability 1, there are $\bar\theta\in\Delta(S)$ and a profile $\bar q$ such that
--
--   $$\theta^k\to\bar\theta,\qquad q^k\to\bar q,\qquad \bar q\in EQ(\bar\theta).$$
--
--   Here $\bar\theta$ is the limit of Lemma 2. Combined with Lemma 2 this gives convergence of the state $(\theta^k,q^k)$ and condition (2b) of Theorem 1.
--
--   Differences from the source:
--   - encoding: $\varphi^s(\cdot|q)$ is a density, continuous in $q$, for $q\in Q$ → $\varphi^s(\cdot|q)$ is a density for every $q\in\prod_i\mathbb R^{d_i}$ and continuous in $q$ everywhere; reason: every instance of the paper extends (compose with the componentwise Euclidean projection onto the closed convex $Q_i$); the dynamics stays in $Q$ almost surely, so only values on $Q$ matter
--   - generalization: $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise, so $u_i^s$ is the mean payoff, continuous in $q$ → $u_i^s$ is any function continuous on $Q$, not tied to $\varphi$; reason: the proof never links $u$ to $\varphi$; taking $u_i^s$ to be the mean of $y_i$ recovers the paper's instances
--   - generalization: players update by $q_i^{k+1}\in F_i(\theta^{k+1},q^k)$ and $y^k\sim\varphi^{s^*}(\cdot|q^k)$ → $q^{k+1}$ is any adapted selection from $F(\theta^{k+1},q^k)$ (possibly randomized), and given the past $\mathcal F_k$ the payoff $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$; reason: a fixed deterministic selection rule with the natural filtration is a special case
--   - encoding: stages $k=1,2,\dots$; update stages $(k_t)$, deterministic or random, with $k_{t+1}-k_t$ finite w.p. 1 → stages indexed from $0$; a set $T(\omega)$ of update stages that contains the first stage and is infinite almost surely; reason: an index shift changes no limit; declaring the first stage an update stage gives the same beliefs as starting from $\theta^1$, and finite gaps w.p. 1 means infinitely many updates
--   - reading: $F_i(\theta,q)$ is upper hemicontinuous in $\theta$ and $q$ → $(\theta,q)\mapsto F_i(\theta,q)$ is upper hemicontinuous (open-set definition) on $\Delta(S)\times Q$; reason: the standard meaning; footnote 4 obtains it from Berge's theorem, which gives joint upper hemicontinuity; no closed or nonempty values are added
--   - reading: the strategy update with static belief $\theta$ converges to an equilibrium → every sequence $q^1\in Q$, $q^{n+1}\in F(\theta,q^n)$ converges to a point of $EQ(\theta)$; reason: the proof applies the assumption to arbitrary selections (construction (9), p.23)
--   - reading: Assumption 3(ii): $\|\theta-\bar\theta\|<\xi_b$ and 'the strategy update $F(\theta,q)$ is unique' → $\bar\theta$ is the $\theta$ of the preamble and the varying belief $\theta'\in\Delta(S)$; unique means $F(\theta',q)$ is a singleton for $q\in Q$; reason: $\bar\theta$ is otherwise undefined in the assumption
--   - encoding: Euclidean norms in Assumption 3 → Lean's sup-type distances on profiles and beliefs; reason: the norms are equivalent and every condition asks only for some radius
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Lemma 3, p.23; proof pp.23–25

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsModel
import Definitions.Def_CoupledLearning_IsLearningProcess
import Definitions.Def_CoupledLearning_belief
import Definitions.Def_CoupledLearning_EQ
import Definitions.Def_CoupledLearning_Assumption1
import Definitions.Def_CoupledLearning_Assumption2
import Definitions.Def_CoupledLearning_Assumption3

open MeasureTheory Filter Topology

namespace CoupledLearning

/-- Lemma 3, arXiv:2206.05637v2, p.23: under Assumptions 1–3, the sequence of strategies
`(q^k)_k` converges with probability 1, and the limit `q̄` lies in `EQ(θ̄)`, where `θ̄` is the
almost-sure limit of the beliefs (Lemma 2). Stated for every model of §2 and every realization of
the learning dynamics with `θ^1(s) > 0` for all `s` and `q^1 ∈ Q`.

**Formalization Note.** `θ̄` and `q̄` depend on the sample point; `θ̄` is tied to Lemma 2 by
asserting the belief convergence in the same existential. -/
theorem lemma_3_strategy_converges
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (φ : S → Prof d → (I → ℝ) → ℝ) (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i))))
    (hmodel : IsModel Q φ u F)
    (hA1 : Assumption1 Q F) (hA2 : Assumption2 Q u F) (hA3 : Assumption3 Q u F)
    (sstar : S) (θ₁ : S → ℝ) (q₁ : Prof d)
    (hθ₁ : θ₁ ∈ stdSimplex ℝ S) (hθ₁_pos : ∀ s, 0 < θ₁ s) (hq₁ : q₁ ∈ Qset Q)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (q : ℕ → Ω → Prof d) (y : ℕ → Ω → (I → ℝ)) (T : Ω → Set ℕ)
    (hproc : IsLearningProcess φ F sstar θ₁ q₁ P ℱ q y T) :
    ∀ᵐ ω ∂P, ∃ θbar ∈ stdSimplex ℝ S, ∃ qbar : Prof d,
      Tendsto (fun k => belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k) atTop
        (𝓝 θbar) ∧
      Tendsto (fun k => q k ω) atTop (𝓝 qbar) ∧
      qbar ∈ EQ Q u θbar := by sorry

end CoupledLearning
