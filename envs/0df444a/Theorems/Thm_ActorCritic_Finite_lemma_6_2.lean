-- Prove2me | Theorems.Thm_ActorCritic_Finite_lemma_6_2
-- name    : ActorCritic.Finite.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:39.753346+00:00
-- url     : https://prove2.me/theorems/b4e02fe7-680f-4c55-90df-d507e3182494
-- title:
--   Lemma 6.2 — convergence of the noise terms e⁽¹⁾_k, e⁽²⁾_k and of ∑ β_k² |H_{θ_k} r_kΓ(r_k)|²
-- statement:
--   Consider the actor–critic algorithm under the hypotheses of Theorem 5.7: Assumptions 2.1 (with data $N$, $x^*$, $\epsilon_0$), 3.1, 3.2, 3.3, and either the TD(1) critic resetting at $x^*$ with Assumption 4.9 at $x^*$, or the TD($\lambda$) critic with $0<\lambda<1$. For every deterministic initial value and every initial law, with probability one:
--   1. the series $\sum_{k=0}^\infty\beta_k\nabla\bar\alpha(\theta_k)\cdot e^{(1)}_k$ converges;
--   2. $\lim_ke^{(2)}_k=0$;
--   3. $\displaystyle\sum_k\beta_k^2\big|H_{\theta_k}(\hat X_k,\hat U_k)r_k\Gamma(r_k)\big|^2<\infty$.
--
--   Together with (6.1) and Lemma 6.1, these are the inputs of the proof of Theorem 3.4: the noise accumulated over a block of iterations vanishes.
--
--   **Formalization Note** "Converges" in (a) is convergence of the partial sums, not absolute summability. Part (c) keeps the index $(\hat X_k,\hat U_k)$ as printed, although (6.1) uses $(\hat X_{k+1},\hat U_{k+1})$; both versions hold. $|\cdot|$ in (c) is the Euclidean norm on $\mathbb R^n$.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), p. 1163, Lemma 6.2 (e⁽¹⁾, e⁽²⁾ on p. 1162)

import Mathlib
import Definitions.Def_ActorCritic_Finite_SteadyState

open MeasureTheory ProbabilityTheory Filter Topology

namespace ActorCritic.Finite

/-- **Lemma 6.2** (convergence of the noise terms; Konda–Tsitsiklis 2003, p. 1163), finite case.
Under the hypotheses of Theorem 5.7 (Assumptions 2.1, 3.1, 3.2, 3.3 with corrected (3.3); TD(1)
at `x*` with Assumption 4.9, or TD(λ) with `0 < λ < 1`), for every initial value and initial law,
almost surely:
(a) the partial sums of `∑_k β_k ∇ᾱ(θ_k) · e^{(1)}_k` converge;
(b) `lim_k e^{(2)}_k = 0`;
(c) `∑_k β_k² |H_{θ_k}(X̂_k, Û_k) r_k Γ(r_k)|² < ∞`. -/
theorem lemma_6_2
    {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    {n m : ℕ} (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ)
    (N : ℕ) (xstar : X) (ε₀ : ℝ)
    (h21a : Assumption21a π) (h21b : Assumption21b π) (h21c : Assumption21c M π)
    (h21d : Assumption21d M π N xstar ε₀)
    (h31 : Assumption31 π φ) (h32 : Assumption32 M π φ)
    (h33a : Assumption33a β γ) (h33b : Assumption33b Γ)
    (crit : Critic X)
    (hcrit : (crit = Critic.td1 xstar ∧ Assumption49 π φ xstar) ∨
      ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ crit = Critic.tdLambda lam)
    (s₀ : ACState n m) (ν₀ : Measure (X × U)) [IsProbabilityMeasure ν₀] :
    ∀ᵐ ω ∂(pathLaw M π φ β γ Γ crit s₀ ν₀),
      (∃ S : ℝ, Tendsto (fun K => ∑ k ∈ Finset.range K,
          β k * inner ℝ (gradient (avgCost M π) (acIter M π φ β γ Γ crit s₀ ω k).θ)
            (noise1 M π φ β γ Γ crit s₀ ω k)) atTop (𝓝 S)) ∧
      Tendsto (fun k => noise2 M π φ β γ Γ crit s₀ ω k) atTop (𝓝 0) ∧
      Summable (fun k => β k ^ 2 *
        ‖(WithLp.toLp 2 ((Hmat π φ (acIter M π φ β γ Γ crit s₀ ω k).θ (ω k)).mulVec
            (fun j => Γ (acIter M π φ β γ Γ crit s₀ ω k).r *
              (acIter M π φ β γ Γ crit s₀ ω k).r j)) : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by sorry

end ActorCritic.Finite
