-- Prove2me | Theorems.Thm_CoupledLearning_eq_7_belief_eq_auxBelief
-- name    : CoupledLearning.eq_7_belief_eq_auxBelief
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:19.379974+00:00
-- url     : https://prove2.me/theorems/6f0ed750-f539-4aae-9d87-0e7786687570
-- title:
--   Identity (7), p.22 — the belief equals the auxiliary belief at update stages and is constant in between
-- statement:
--   Throughout, $I$ is a finite set of players, player $i$ chooses $q_i$ in a convex, closed and bounded set $Q_i\subseteq\mathbb R^{d_i}$, $Q=\prod_i Q_i$, and $S$ is a finite set of parameters with true parameter $s^*$. For each $s\in S$ and $q$, $\varphi^s(\cdot|q)$ is a probability density of payoff vectors $y\in\mathbb R^I$, continuous in $q$; $u_i^s$ is continuous on $Q$; and $F_i(\theta,q)\subseteq Q_i$ is player $i$'s set of updated strategies. The initial belief $\theta^1\in\Delta(S)$ has $\theta^1(s)>0$ for every $s$ and $q^1\in Q$. On a probability space with filtration $(\mathcal F_k)$: $q^k$ is $\mathcal F_k$-measurable, $y^k$ is $\mathcal F_{k+1}$-measurable and has conditional density $\varphi^{s^*}(\cdot|q^k)$ given $\mathcal F_k$, the belief $\theta^k$ is computed by (θ-update) at the update stages $k_1<k_2<\cdots$ (infinitely many) and is constant in between, and $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$.
--
--   Let $\tilde\theta^k$ be the auxiliary belief (6), updated at every stage. Then, almost surely, for every stage $k$,
--
--   $$\theta^k=\begin{cases}\tilde\theta^k, & k=k_t\text{ for some }t,\\ \theta^{k-1}, & \text{otherwise.}\end{cases}$$
--
--   This reduces every statement about the intermittently updated belief to the auxiliary belief observed along the update stages.
--
--   Differences from the source:
--   - encoding: $\varphi^s(\cdot|q)$ is a density, continuous in $q$, for $q\in Q$ → $\varphi^s(\cdot|q)$ is a density for every $q\in\prod_i\mathbb R^{d_i}$ and continuous in $q$ everywhere; reason: every instance of the paper extends (compose with the componentwise Euclidean projection onto the closed convex $Q_i$); the dynamics stays in $Q$ almost surely, so only values on $Q$ matter
--   - generalization: $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise, so $u_i^s$ is the mean payoff, continuous in $q$ → $u_i^s$ is any function continuous on $Q$, not tied to $\varphi$; reason: the proof never links $u$ to $\varphi$; taking $u_i^s$ to be the mean of $y_i$ recovers the paper's instances
--   - generalization: players update by $q_i^{k+1}\in F_i(\theta^{k+1},q^k)$ and $y^k\sim\varphi^{s^*}(\cdot|q^k)$ → $q^{k+1}$ is any adapted selection from $F(\theta^{k+1},q^k)$ (possibly randomized), and given the past $\mathcal F_k$ the payoff $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$; reason: a fixed deterministic selection rule with the natural filtration is a special case
--   - encoding: stages $k=1,2,\dots$; update stages $(k_t)$, deterministic or random, with $k_{t+1}-k_t$ finite w.p. 1 → stages indexed from $0$; a set $T(\omega)$ of update stages that contains the first stage and is infinite almost surely; reason: an index shift changes no limit; declaring the first stage an update stage gives the same beliefs as starting from $\theta^1$, and finite gaps w.p. 1 means infinitely many updates
--   - generalization: Identity (7) is stated in the paper under its standing Assumptions 1–3 → Assumptions 1–3 are not assumed; reason: the proof does not use them; with them the statement is the paper's
--   - encoding: (7) as an identity → (7) almost surely; reason: the normalizers of (6) and (θ-update) are positive only almost surely; where one vanishes the printed formulas are undefined (Lean's division returns 0)
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, eq. (7), p.22

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsModel
import Definitions.Def_CoupledLearning_IsLearningProcess
import Definitions.Def_CoupledLearning_belief
import Definitions.Def_CoupledLearning_auxBelief

open MeasureTheory

namespace CoupledLearning

/-- Identity (7), arXiv:2206.05637v2, p.22: from (θ-update), `θ^k = θ̃^k` if `k = k_t` for some
`t`, and `θ^k = θ^{k−1}` otherwise, where `θ̃` is the auxiliary belief (6) updated at every
stage. Stated for every model of §2 and every realization of the learning dynamics with
`θ^1(s) > 0` for all `s` and `q^1 ∈ Q`.

**Formalization Note.** Stages are indexed from `0`. The identity is asserted almost surely: the
normalizers of (6) and (θ-update) are positive only almost surely, and where one vanishes the
printed formulas are undefined (Lean's division returns `0`). Assumptions 1–3 are not needed and
not assumed. -/
theorem eq_7_belief_eq_auxBelief
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
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      (k ∈ T ω → belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k =
        auxBelief θ₁ φ (fun j => q j ω) (fun j => y j ω) k) ∧
      (k + 1 ∉ T ω → belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) (k + 1) =
        belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k) := by sorry

end CoupledLearning
