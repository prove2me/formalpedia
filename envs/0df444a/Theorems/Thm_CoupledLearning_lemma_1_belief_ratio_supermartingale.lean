-- Prove2me | Theorems.Thm_CoupledLearning_lemma_1_belief_ratio_supermartingale
-- name    : CoupledLearning.lemma_1_belief_ratio_supermartingale
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:06.521547+00:00
-- url     : https://prove2.me/theorems/9595e4c6-b391-48e9-93b8-2222bf339eea
-- title:
--   Lemma 1, p.22 — the belief ratio is a supermartingale (corrected: supermartingale; martingale when $\varphi^s\ll\varphi^{s^*}$)
-- statement:
--   Throughout, $I$ is a finite set of players, player $i$ chooses $q_i$ in a convex, closed and bounded set $Q_i\subseteq\mathbb R^{d_i}$, $Q=\prod_i Q_i$, and $S$ is a finite set of parameters with true parameter $s^*$. For each $s\in S$ and $q$, $\varphi^s(\cdot|q)$ is a probability density of payoff vectors $y\in\mathbb R^I$, continuous in $q$; $u_i^s$ is continuous on $Q$; and $F_i(\theta,q)\subseteq Q_i$ is player $i$'s set of updated strategies. The initial belief $\theta^1\in\Delta(S)$ has $\theta^1(s)>0$ for every $s$ and $q^1\in Q$. On a probability space with filtration $(\mathcal F_k)$: $q^k$ is $\mathcal F_k$-measurable, $y^k$ is $\mathcal F_{k+1}$-measurable and has conditional density $\varphi^{s^*}(\cdot|q^k)$ given $\mathcal F_k$, the belief $\theta^k$ is computed by (θ-update) at the update stages $k_1<k_2<\cdots$ (infinitely many) and is constant in between, and $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$.
--
--   Let $\tilde\theta^k$ be the auxiliary belief (6). For every $s\in S$:
--
--   1. the belief ratios $\big(\tilde\theta^k(s)/\tilde\theta^k(s^*)\big)_k$ form a supermartingale with respect to $(\mathcal F_k)$;
--   2. if $\varphi^s(\cdot|q)\ll\varphi^{s^*}(\cdot|q)$ for every $q\in Q$, they form a martingale.
--
--   Since the ratios are nonnegative, they converge almost surely, which gives the convergence of beliefs (Lemma 2).
--
--   **Formalization Note** Mathlib's supermartingale and martingale include adaptedness and integrability of every term. Where $\tilde\theta^k(s^*)=0$ (a null set) Lean's division returns $0$.
--
--   Differences from the source:
--   - encoding: $\varphi^s(\cdot|q)$ is a density, continuous in $q$, for $q\in Q$ → $\varphi^s(\cdot|q)$ is a density for every $q\in\prod_i\mathbb R^{d_i}$ and continuous in $q$ everywhere; reason: every instance of the paper extends (compose with the componentwise Euclidean projection onto the closed convex $Q_i$); the dynamics stays in $Q$ almost surely, so only values on $Q$ matter
--   - generalization: $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise, so $u_i^s$ is the mean payoff, continuous in $q$ → $u_i^s$ is any function continuous on $Q$, not tied to $\varphi$; reason: the proof never links $u$ to $\varphi$; taking $u_i^s$ to be the mean of $y_i$ recovers the paper's instances
--   - generalization: players update by $q_i^{k+1}\in F_i(\theta^{k+1},q^k)$ and $y^k\sim\varphi^{s^*}(\cdot|q^k)$ → $q^{k+1}$ is any adapted selection from $F(\theta^{k+1},q^k)$ (possibly randomized), and given the past $\mathcal F_k$ the payoff $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$; reason: a fixed deterministic selection rule with the natural filtration is a special case
--   - encoding: stages $k=1,2,\dots$; update stages $(k_t)$, deterministic or random, with $k_{t+1}-k_t$ finite w.p. 1 → stages indexed from $0$; a set $T(\omega)$ of update stages that contains the first stage and is infinite almost surely; reason: an index shift changes no limit; declaring the first stage an update stage gives the same beliefs as starting from $\theta^1$, and finite gaps w.p. 1 means infinitely many updates
--   - generalization: Lemma 1 is stated in the paper under its standing Assumptions 1–3 → Assumptions 1–3 are not assumed; reason: the proof does not use them; with them the statement is the paper's
--   - correction: the ratios $\tilde\theta^k(s)/\tilde\theta^k(s^*)$ form a martingale → (a) a supermartingale; (b) a martingale if $\varphi^s(\cdot|q)\ll\varphi^{s^*}(\cdot|q)$ for every $q\in Q$; reason: counterexample E5: $\varphi^{s^*}=g(z)$, $\varphi^s=g(z/2)/2$ with $g$, $z$ as in E4; the expected likelihood ratio is $\int_{\varphi^{s^*}>0}\varphi^s=3/4$, because the proof's computation $\int\varphi^s=1$ ignores the set where $\varphi^{s^*}=0$
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Lemma 1, p.22; proof p.40, eq. (27)

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsModel
import Definitions.Def_CoupledLearning_IsLearningProcess
import Definitions.Def_CoupledLearning_belief
import Definitions.Def_CoupledLearning_auxBelief
import Definitions.Def_CoupledLearning_payoffMeasure

open MeasureTheory

namespace CoupledLearning

/-- Lemma 1, arXiv:2206.05637v2, p.22, corrected. The page states that for any `s ∈ S` the
belief ratios `(θ̃^k(s)/θ̃^k(s*))_k` form a martingale. As corrected:

(a) for every `s`, the ratio process is a supermartingale with respect to `ℱ`;
(b) if `φ^s(·|q) ≪ φ^{s*}(·|q)` for every `q ∈ Q`, it is a martingale.

**Formalization Note.** The printed martingale claim is false: with one player, `Q = [0, 1]`,
`z = y + q`, `g(z) = max(0, 1 − |z|)`, `φ^{s*}(y|q) = g(z)` and `φ^s(y|q) = g(z/2)/2`, the expected
likelihood ratio is `∫_{φ^{s*} > 0} φ^s = 3/4`. Stages are indexed from `0`. Mathlib's
`Supermartingale`/`Martingale` include adaptedness and integrability of every term. Assumptions
1–3 are not needed and not assumed. -/
theorem lemma_1_belief_ratio_supermartingale
    {I S : Type*} [Fintype I] [Fintype S] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (φ : S → Prof d → (I → ℝ) → ℝ) (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i))))
    (hmodel : IsModel Q φ u F)
    (sstar : S) (θ₁ : S → ℝ) (q₁ : Prof d)
    (hθ₁ : θ₁ ∈ stdSimplex ℝ S) (hθ₁_pos : ∀ s, 0 < θ₁ s) (hq₁ : q₁ ∈ Qset Q)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (q : ℕ → Ω → Prof d) (y : ℕ → Ω → (I → ℝ)) (T : Ω → Set ℕ)
    (hproc : IsLearningProcess φ F sstar θ₁ q₁ P ℱ q y T) (s : S) :
    Supermartingale
        (fun k ω => auxBelief θ₁ φ (fun j => q j ω) (fun j => y j ω) k s /
          auxBelief θ₁ φ (fun j => q j ω) (fun j => y j ω) k sstar) ℱ P ∧
      ((∀ q' ∈ Qset Q, payoffMeasure φ s q' ≪ payoffMeasure φ sstar q') →
        Martingale
          (fun k ω => auxBelief θ₁ φ (fun j => q j ω) (fun j => y j ω) k s /
            auxBelief θ₁ φ (fun j => q j ω) (fun j => y j ω) k sstar) ℱ P) := by sorry

end CoupledLearning
