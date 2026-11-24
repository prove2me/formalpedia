-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_theorem_5
-- name    : AvgRewardPMD.SPMD.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:29:26.654007+00:00
-- url     : https://prove2.me/theorems/09cd0d0a-ba33-4ee4-aae8-e57079939063
-- title:
--   Theorem 5, p. 22 — VRTD squared D-norm bias (4.20) with universal constants b₁, b₂
-- statement:
--   There exist positive universal constants $b_1,b_2$ with the following property. Fix a finite mixing and ergodic AMDP, a strictly positive feasible policy $\pi$, its stationary law $\nu$, and the overall critic cost $|c(s,a)|\le\bar c$ of §4. Use the normalized independent features $\Psi$ of §4.2.1 with positive feature dimension and $\mathbf1\notin\mathrm{range}(\Psi)$. Let $\theta^*$ solve (4.6), and let $D,\mu,1-\beta,C_P,\varrho,C_{\max},W_1$ have exactly the definitions used in Theorem 4.
--
--   Run Algorithm 3 from the deterministic input $\hat\theta_0$ for $K\ge1$ epochs on a single Markov trajectory with arbitrary initial law. Use positive stepsize $\eta$, positive integer skips $\tau,\tau'$, the fixed batch sizes $N_k=N$, $N'_k=N'$, and
--   $$\eta\le\frac{1-\beta}{845},\qquad T\ge\frac{64}{\mu(1-\beta)\eta},\qquad N\ge\frac{1160}{\mu(1-\beta)^2},\qquad N'\ge\frac1{\mu(1-\beta)^2}.$$
--   The fixed batches also meet the geometric batch lower bounds of (4.16). Then
--   $$\|\Psi\mathbb E[\hat\theta_K]-\Psi\theta^*\|_D^2\le 2^{-K}\|\Psi\hat\theta_0-\Psi\theta^*\|_D^2+\left(b_1 C_{\max}^2\varrho^{2\tau'}+\frac{b_2 C_{\max}\varrho^\tau}{(1-\beta)\sqrt\mu}\right)\left(\|\Psi\hat\theta_0-\Psi\theta^*\|_D^2+\frac{W_1}{N}+\bar c^2\right).\tag{4.20}$$
--   This controls the squared bias, rather than the mean squared error of Theorem 4. The constants are chosen before the MDP, feature dimension, trajectory, batch sizes and all tuning parameters; the source does not assign them numerical values.
--
--   **Formalization Note** The expectation is the vector Bochner integral of the output of the same explicit Algorithm 3 used in Theorem 4. Finite observations have finite range, hence the output is measurable, bounded and integrable. Theorem 5 cites (4.16) and (4.19), not (4.17); no additional skip bound is imposed.
--
--   Differences from the source:
--   - encoding: P = P^π, ν = ν^π → P the state–action matrix of π, ν any stationary distribution of P_π; reason: under Assumption 2 the stationary distribution is unique
--   - encoding: d linearly independent basis vectors ψ_1, …, ψ_d → d ≥ 1 and linearly independent columns of Ψ; reason: the source uses a least eigenvalue and a unit-sphere infimum, which are undefined for the zero-dimensional feature space; d ≥ 1 makes their ordinary source domain explicit
--   - encoding: (4.5) π(s|a) ≥ π̲ > 0 for some π̲ → π s a > 0 for all s, a; reason: equivalent on finite S × A
--   - encoding: θ*, the unique solution of (4.6) → any θ* solving (4.6); reason: the paper cites Tsitsiklis–Van Roy (1999) Theorem 1 for existence and uniqueness, so the solution set is the singleton {θ*}
--   - reading: C_P, ϱ, the constants of Lemma 7 → any C_P > 0, ϱ ∈ (0,1) satisfying the conclusion of Lemma 7 for every policy (t ≥ 1); reason: Theorem 4 uses Lemma 7 only through that property; Lemma 7 provides such a pair
--   - reading: each sample is "the last one of τ′+1 (τ+1) successive samples" of a single trajectory → the explicit positions of the VRTD definition: blocks of τ′+1 (τ+1) consecutive positions, consumed in order, epoch after epoch; reason: the source fixes the block lengths and the order of consumption but not an index formula
--   - reading: τ, τ′, N_k, N′_k ∈ Z+, N, N′ positive → τ, τ′, N, N′ ≥ 1 (N_k, N′_k ≥ 1 follow from (4.16)); reason: Z+ denotes positive integers in Algorithm 3
--   - encoding: E[‖Q̄* − Ψθ*‖²_D] in W₁ → ‖Q̄* − Ψθ*‖²_D; reason: Q̄* and θ* are deterministic, so the expectation is the value itself
--   - encoding: μ = λ_min(B) → the minimum of θᵀBθ over the unit sphere; reason: B is symmetric, so this is its least eigenvalue
--   - encoding: ρ* = ρ^π → avgCost of π and c at a start state s₀; reason: under Assumption 1 the average cost does not depend on the start state
--   - encoding: conditions (4.16), N_k=N, N′_k=N′, and (4.19) → the η,T conditions of (4.16), fixed batches N,N′, and the two thresholds of (4.19); reason: the remaining (4.16) batch inequalities follow because 0 < 3/4 ≤ 1 and 1 ≤ k ≤ K; no instance is excluded
--   - encoding: b₁ and b₂ are universal constants → ∃ b₁ b₂ > 0 before all types and instance parameters; reason: existential quantification preserves the unspecified absolute constants; choosing numerical values is unnecessary, and a larger positive pair preserves the bound
--   - encoding: K epochs of Algorithm 3 → K ≥ 1; reason: K is a positive epoch count in the algorithm setting; the theorem concerns an output after running those epochs
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 22, Theorem 5, (4.19)–(4.20); Appendix A.6, pp. 43–46

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_VRTD

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory Matrix

theorem theorem_5 :
    ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧
    ∀ (S A : Type*) [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (herg : IsErgodic P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (hπpos : ∀ s a, 0 < π s a)
    (ν : S → ℝ) (hν : MarkovMixing.IsStationary (stateMatrix P π) ν)
    (c : S → A → ℝ) (cbar : ℝ) (hc : ∀ s a, |c s a| ≤ cbar) (s₀ : S)
    (d : ℕ) (hd : 0 < d) (Ψ : Matrix (S × A) (Fin d) ℝ)
    (hlin : LinearIndependent ℝ Ψᵀ) (hfeat : ∀ x, ∑ i, Ψ x i ^ 2 ≤ 1)
    (hone : ∀ θ : Fin d → ℝ, Ψ *ᵥ θ ≠ fun _ => 1)
    (θstar : Fin d → ℝ)
    (hθstar : gram ν π Ψ *ᵥ θstar
      = Ψᵀ *ᵥ (fun y => saWeight ν π y * (saTransition P π *ᵥ (Ψ *ᵥ θstar)) y)
        + Ψᵀ *ᵥ (fun y => saWeight ν π y * (c y.1 y.2 - avgCost P π c s₀)))
    (CP ϱ : ℝ) (hCP : 0 < CP) (hϱ0 : 0 < ϱ) (hϱ1 : ϱ < 1)
    (hmixing : ∀ π' : S → A → ℝ, IsPolicy π' →
      ∀ ν' : S → ℝ, MarkovMixing.IsStationary (stateMatrix P π') ν' →
        (∀ s, 0 < ν' s) ∧
        ∀ t : ℕ, 1 ≤ t → ∀ s : S,
          ∑ s', |((stateMatrix P π') ^ t) s s' - ν' s'| ≤ CP * ϱ ^ t)
    (Ω : Type*) (m : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → S × A) (hX : IsSAMarkovChain μ P π X)
    (K N N' : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (η : ℝ) (hη0 : 0 < η) (T τ τ' : ℕ) (hτ : 1 ≤ τ) (hτ' : 1 ≤ τ')
    (θ0 : Fin d → ℝ)
    (h416 : η ≤ dirichletGap P π ν Ψ / 845 ∧
      (T : ℝ) ≥ 64 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ * η))
    (h419 : (N : ℝ) ≥ 1160 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ ^ 2) ∧
      (N' : ℝ) ≥ 1 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ ^ 2)),
    dNormSq ν π
      (Ψ *ᵥ (∫ ω, (vrtd c Ψ η τ τ' T (fun _ => N) (fun _ => N') θ0 (fun j => X j ω) K).1 ∂μ)
        - Ψ *ᵥ θstar)
      ≤ 1 / 2 ^ K * dNormSq ν π (Ψ *ᵥ θ0 - Ψ *ᵥ θstar)
        + (b₁ * constCmax CP P π ν Ψ ^ 2 * ϱ ^ (2 * τ')
          + b₂ * constCmax CP P π ν Ψ * ϱ ^ τ
            / (dirichletGap P π ν Ψ * Real.sqrt (minEig (gram ν π Ψ))))
          * (dNormSq ν π (Ψ *ᵥ θ0 - Ψ *ᵥ θstar)
            + constW1 P π ν c Ψ θstar / N + cbar ^ 2) := by sorry

end AvgRewardPMD.SPMD.Supplement
