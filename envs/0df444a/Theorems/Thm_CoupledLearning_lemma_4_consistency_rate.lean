-- Prove2me | Theorems.Thm_CoupledLearning_lemma_4_consistency_rate
-- name    : CoupledLearning.lemma_4_consistency_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:54.118308+00:00
-- url     : https://prove2.me/theorems/51c53b82-8f2e-4284-9a73-8309acf73c5f
-- title:
--   Lemma 4, p.25 — consistency, rate and exclusion at the limit (corrected: rate (3) and finite-time exclusion)
-- statement:
--   Throughout, $I$ is a finite set of players, player $i$ chooses $q_i$ in a convex, closed and bounded set $Q_i\subseteq\mathbb R^{d_i}$, $Q=\prod_i Q_i$, and $S$ is a finite set of parameters with true parameter $s^*$. For each $s\in S$ and $q$, $\varphi^s(\cdot|q)$ is a probability density of payoff vectors $y\in\mathbb R^I$, continuous in $q$; $u_i^s$ is continuous on $Q$; and $F_i(\theta,q)\subseteq Q_i$ is player $i$'s set of updated strategies. The initial belief $\theta^1\in\Delta(S)$ has $\theta^1(s)>0$ for every $s$ and $q^1\in Q$. On a probability space with filtration $(\mathcal F_k)$: $q^k$ is $\mathcal F_k$-measurable, $y^k$ is $\mathcal F_{k+1}$-measurable and has conditional density $\varphi^{s^*}(\cdot|q^k)$ given $\mathcal F_k$, the belief $\theta^k$ is computed by (θ-update) at the update stages $k_1<k_2<\cdots$ (infinitely many) and is constant in between, and $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$.
--
--   Assume Assumptions 1–3. With probability 1 the state converges, $\theta^k\to\bar\theta\in\Delta(S)$ and $q^k\to\bar q$, and:
--
--   1. **(2a)** $[\bar\theta]\subseteq S^*(\bar q)$;
--   2. **rate (3), corrected.** For every $s\notin S^*(\bar q)$ with $\varphi^{s^*}(\cdot|\bar q)\ll\varphi^s(\cdot|\bar q)$: if $q\mapsto D_{KL}(\varphi^{s^*}(\cdot|q)\|\varphi^s(\cdot|q))$ is continuous at $\bar q$ within $Q$, if $\int\varphi^{s^*}(y|q)\log^2\frac{\varphi^s(y|q)}{\varphi^{s^*}(y|q)}\,dy\le M$ for all $q\in Q$ near $\bar q$, and if $k_t/k\to1$ for the last update stage $k_t\le k$, then either $\theta^k(s)=0$ for all large $k$, or $\theta^k(s)>0$ for all $k$ and
--   $$\lim_{k\to\infty}\frac1k\log\theta^k(s)=-D_{KL}\big(\varphi^{s^*}(y|\bar q)\,\|\,\varphi^s(y|\bar q)\big);$$
--   3. **exclusion, corrected.** For every $s\notin S^*(\bar q)$ with $\varphi^{s^*}(\cdot|\bar q)\not\ll\varphi^s(\cdot|\bar q)$: if $q\mapsto\Pr_{y\sim\varphi^{s^*}(\cdot|q)}(\varphi^s(y|q)=0)$ is lower semicontinuous at $\bar q$ within $Q$, there is a finite $K^*$ with $\theta^k(s)=0$ for all $k>K^*$.
--
--   The limit, $K^*$ and all conditions in items 2–3 depend on the sample path.
--
--   **Formalization Note** $\frac1k\log\theta^k(s)$ is `Real.log (θ^k(s)) / k` with stages indexed from $0$; the second-moment bound makes $D_{KL}$ finite at $\bar q$, so its real value is used. The second-moment integral is a lower Lebesgue integral of a nonnegative integrand.
--
--   Differences from the source:
--   - encoding: $\varphi^s(\cdot|q)$ is a density, continuous in $q$, for $q\in Q$ → $\varphi^s(\cdot|q)$ is a density for every $q\in\prod_i\mathbb R^{d_i}$ and continuous in $q$ everywhere; reason: every instance of the paper extends (compose with the componentwise Euclidean projection onto the closed convex $Q_i$); the dynamics stays in $Q$ almost surely, so only values on $Q$ matter
--   - generalization: $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise, so $u_i^s$ is the mean payoff, continuous in $q$ → $u_i^s$ is any function continuous on $Q$, not tied to $\varphi$; reason: the proof never links $u$ to $\varphi$; taking $u_i^s$ to be the mean of $y_i$ recovers the paper's instances
--   - generalization: players update by $q_i^{k+1}\in F_i(\theta^{k+1},q^k)$ and $y^k\sim\varphi^{s^*}(\cdot|q^k)$ → $q^{k+1}$ is any adapted selection from $F(\theta^{k+1},q^k)$ (possibly randomized), and given the past $\mathcal F_k$ the payoff $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$; reason: a fixed deterministic selection rule with the natural filtration is a special case
--   - encoding: stages $k=1,2,\dots$; update stages $(k_t)$, deterministic or random, with $k_{t+1}-k_t$ finite w.p. 1 → stages indexed from $0$; a set $T(\omega)$ of update stages that contains the first stage and is infinite almost surely; reason: an index shift changes no limit; declaring the first stage an update stage gives the same beliefs as starting from $\theta^1$, and finite gaps w.p. 1 means infinitely many updates
--   - encoding: $D_{KL}$ of Definition 1 (integral if $\ll$, else $\infty$) → Mathlib's `klDiv` of the two payoff distributions, in $[0,\infty]$; reason: equal on every pair of densities: when the log-likelihood ratio is not integrable both are $+\infty$
--   - reading: $F_i(\theta,q)$ is upper hemicontinuous in $\theta$ and $q$ → $(\theta,q)\mapsto F_i(\theta,q)$ is upper hemicontinuous (open-set definition) on $\Delta(S)\times Q$; reason: the standard meaning; footnote 4 obtains it from Berge's theorem, which gives joint upper hemicontinuity; no closed or nonempty values are added
--   - reading: the strategy update with static belief $\theta$ converges to an equilibrium → every sequence $q^1\in Q$, $q^{n+1}\in F(\theta,q^n)$ converges to a point of $EQ(\theta)$; reason: the proof applies the assumption to arbitrary selections (construction (9), p.23)
--   - reading: Assumption 3(ii): $\|\theta-\bar\theta\|<\xi_b$ and 'the strategy update $F(\theta,q)$ is unique' → $\bar\theta$ is the $\theta$ of the preamble and the varying belief $\theta'\in\Delta(S)$; unique means $F(\theta',q)$ is a singleton for $q\in Q$; reason: $\bar\theta$ is otherwise undefined in the assumption
--   - encoding: Euclidean norms in Assumption 3 → Lean's sup-type distances on profiles and beliefs; reason: the norms are equivalent and every condition asks only for some radius
--   - reading: 'Any fix point $(\bar\theta,\bar q)$ satisfies (2a)' → the almost-sure limit $(\bar\theta,\bar q)$ of the dynamics satisfies (2a); reason: every element of $\Omega$ satisfies (2a) by definition, so the literal reading is empty; the proof (pp.25–27) is about the limit of Lemmas 2–3
--   - correction: (3): $\lim_k \frac1k\log\theta^k(s)=-D_{KL}$ w.p. 1 → either $\theta^k(s)=0$ for all large $k$, or $\theta^k(s)>0$ for all $k$ and (3) holds; reason: counterexample E4: one player, $Q=[0,1]$, $F(\theta,q)=\{q/2\}$, $z=y+q$, $g(z)=\max(0,1-|z|)$, $h(z)=\max(0,|z|-1/4)$, $\varphi^{s^*}=g(z)$, $\varphi^s\propto g(z)(\max(0,1/2-q)+h(z))$; from $q^1=1$, $y^1$ falls where $\varphi^s=0$ with positive probability, so $\theta^k(s)=0$ for $k\ge2$ although $\varphi^{s^*}(\cdot|0)\ll\varphi^s(\cdot|0)$ and $0<D_{KL}<\infty$
--   - correction: (3) under update gaps $k_{t+1}-k_t$ finite w.p. 1 → (3) is asserted on paths with $k_{t+1}/k_t\to1$ (written $k_t/k\to1$ for the last update stage $k_t\le k$); reason: counterexample E2: $\varphi^s(\cdot|q)=N(s-q,1)$, $S=\{0,1\}$, $s^*=0$, $F=\{q/2\}$, updates at $k_t=2^{t-1}$; $\frac1k\log\theta^k(1)$ oscillates between about $-1/2$ and $-1/4$
--   - correction: (3) whenever $\varphi^{s^*}(\cdot|\bar q)\ll\varphi^s(\cdot|\bar q)$ → (3) additionally assumes that $q\mapsto D_{KL}(\varphi^{s^*}(\cdot|q)\|\varphi^s(\cdot|q))$ is continuous at $\bar q$ within $Q$ and that $\int\varphi^{s^*}(y|q)\log^2(\varphi^s(y|q)/\varphi^{s^*}(y|q))\,dy$ is bounded for $q\in Q$ near $\bar q$; reason: counterexample E3: a Gaussian pair with a shrinking bump in $\varphi^s$, continuous in $q$ pointwise, hit infinitely often along $q^j=2^{1-j}$, so $\frac1j\log\theta^{j}(s)\le -D_{KL}-A+o(1)$ infinitely often; the proof's law of large numbers for non-i.i.d. log-likelihood ratios needs this regularity
--   - correction: 'Otherwise' (no absolute continuity at $\bar q$): $\theta^k(s)=0$ for all $k>K^*$ w.p. 1 → the clause additionally assumes that $q\mapsto\Pr_{y\sim\varphi^{s^*}(\cdot|q)}(\varphi^s(y|q)=0)$ is lower semicontinuous at $\bar q$ within $Q$; reason: counterexample E1: as E4 with $\varphi^s\propto g(z)(q+h(z))$; $\varphi^s(\cdot|q)>0$ wherever $g>0$ for $q>0$, so along $q^k=2^{1-k}$ the belief $\theta^k(s)$ stays positive a.s. although absolute continuity fails at $\bar q=0$; the proof's claim that this probability is continuous in $q$ is false
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Lemma 4, p.25; proof pp.25–27

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsModel
import Definitions.Def_CoupledLearning_IsLearningProcess
import Definitions.Def_CoupledLearning_belief
import Definitions.Def_CoupledLearning_EQ
import Definitions.Def_CoupledLearning_Assumption1
import Definitions.Def_CoupledLearning_Assumption2
import Definitions.Def_CoupledLearning_Assumption3
import Definitions.Def_CoupledLearning_payoffMeasure
import Definitions.Def_CoupledLearning_KL
import Definitions.Def_CoupledLearning_payoffEquivSet
import Definitions.Def_CoupledLearning_beliefSupport

open MeasureTheory Filter Topology

namespace CoupledLearning

/-- Lemma 4, arXiv:2206.05637v2, p.25, corrected: the fixed point `(θ̄, q̄)` reached by the
dynamics satisfies (2a), `[θ̄] ⊆ S*(q̄)`. Furthermore, for any `s ∈ S \ S*(q̄)`, if
`φ^{s*}(·|q̄) ≪ φ^s(·|q̄)` then `θ^k(s)` satisfies (3),
`lim_k (1/k) log θ^k(s) = −D_KL(φ^{s*}(·|q̄) ‖ φ^s(·|q̄))`; otherwise there is a finite `K*` with
`θ^k(s) = 0` for all `k > K*`, with probability 1. Stated under Assumptions 1–3 for every model
of §2 and every realization of the learning dynamics with `θ^1(s) > 0` and `q^1 ∈ Q`.

Corrections (the printed clauses are false, see the counterexamples in the item description):
(C0) in clause (3) `θ^k(s)` may reach `0`, after which `log θ^k(s)` is `−∞`; the clause is
asserted as "`θ^k(s) = 0` eventually, or `θ^k(s) > 0` for all `k` and (3) holds";
(C1) clause (3) assumes `k_{t+1}/k_t → 1` along the path (finite gaps do not suffice);
(C2) clause (3) assumes that `q ↦ D_KL(φ^{s*}(·|q) ‖ φ^s(·|q))` is continuous at `q̄` within `Q`
and that `∫ φ^{s*}(y|q) (log(φ^s(y|q)/φ^{s*}(y|q)))² dy` is bounded for `q ∈ Q` near `q̄`;
(C3) the "otherwise" clause assumes that `q ↦ Pr_{y∼φ^{s*}(·|q)}(φ^s(y|q) = 0)` is lower
semicontinuous at `q̄` within `Q`.

"Any fix point `(θ̄, q̄)`" is read as the almost-sure limit of the dynamics (Lemmas 2–3).

**Formalization Note.** Stages are indexed from `0`; `(1/k) log θ^k(s)` is
`Real.log (θ^k(s)) / k`, and every limit is unchanged by the shift. `θ̄`, `q̄` and `K*` depend on
the sample point, and every condition of the corrected clauses is a condition at `q̄` or along the
sample path, inside the almost-sure statement. `lastUpdate (T ω) k` is the last update stage
`k_t ≤ k`; `k_t/k → 1` is equivalent to `k_{t+1}/k_t → 1`. `D_KL` is finite at `q̄` under the
second-moment condition, so its `.toReal` is the true value. -/
theorem lemma_4_consistency_rate
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
      beliefSupport θbar ⊆ payoffEquivSet φ sstar qbar ∧
      ∀ s ∉ payoffEquivSet φ sstar qbar,
        (payoffMeasure φ sstar qbar ≪ payoffMeasure φ s qbar →
          ContinuousWithinAt (fun q' => KL φ sstar s q') (Qset Q) qbar →
          (∃ U ∈ 𝓝[Qset Q] qbar, ∃ M : ℝ, ∀ q' ∈ U,
            ∫⁻ z, ENNReal.ofReal (φ sstar q' z * Real.log (φ s q' z / φ sstar q' z) ^ 2)
              ≤ ENNReal.ofReal M) →
          Tendsto (fun k : ℕ => (lastUpdate (T ω) k : ℝ) / k) atTop (𝓝 1) →
          (∃ K : ℕ, ∀ k > K, belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k s = 0) ∨
          ((∀ k, 0 < belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k s) ∧
            Tendsto
              (fun k : ℕ => Real.log (belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k s) / k)
              atTop (𝓝 (-(KL φ sstar s qbar).toReal)))) ∧
        (¬ payoffMeasure φ sstar qbar ≪ payoffMeasure φ s qbar →
          LowerSemicontinuousWithinAt
            (fun q' => payoffMeasure φ sstar q' {z | φ s q' z = 0}) (Qset Q) qbar →
          ∃ K : ℕ, ∀ k > K, belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) k s = 0) := by sorry

end CoupledLearning
