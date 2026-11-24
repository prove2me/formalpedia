-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_theorem_4
-- name    : AvgRewardPMD.SPMD.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:28:49.155276+00:00
-- url     : https://prove2.me/theorems/2f56162e-55c9-493e-95e2-de01b61bd581
-- title:
--   Theorem 4, p. 21 — VRTD under (4.16)–(4.17): E[(ρ̂_K−ρ*)²] ≤ 5c̄²/N′ and E‖Ψθ̂_K−Ψθ*‖²_D ≤ 2^{−K}‖Ψθ̂_0−Ψθ*‖²_D + 3W₁/N + 108c̄²/(N′(1−β)²μ) + 3c̄²/(4N′)
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying Assumptions 1 and 2, with cost $|c(s,a)|\le\bar c$ ($c$ is the overall cost of §4). Fix a policy $\pi$ with $\pi(a\mid s)>0$ for all $s,a$, its state–action matrix $P=P^\pi$, its stationary distribution $\nu$, $D=\mathrm{diag}(\nu(s)\pi(a\mid s))$ and its average cost $\rho^*=\rho^\pi$. Let $\psi_1,\dots,\psi_d$ ($d\ge1$) be linearly independent features with $\|\psi(s,a)\|_2\le1$ and $\mathbf 1\notin\mathcal S$, and let $\theta^*$ solve the projected Bellman equation $\Psi^\top D\Psi\theta^*=\Psi^\top DP\Psi\theta^*+\Psi^\top D(c-\rho^*\mathbf 1)$ (4.6). Let $C_P>0$ and $\varrho\in(0,1)$ be constants as in Lemma 7, and let $1-\beta$, $\mu$, $M$, $\bar Q^*$, $\bar\Sigma$, $W_1$, $C_M$, $C_{\max}$ be as in §4.2.1.
--
--   Run VRTD (Algorithm 3) from $\hat\theta_0$ on a single trajectory of the state–action chain $P$ started from an arbitrary initial law, for $K\ge1$ epochs, with positive integers $N,N',\tau,\tau'$, and assume that for every epoch $k\in[K]$
--   $$\eta\le\frac{1-\beta}{845},\quad T\ge\frac{64}{\mu(1-\beta)\eta},\quad N_k\ge\max\Big\{\frac{1160}{\mu(1-\beta)^2},\Big(\frac34\Big)^{K-k}N\Big\},\quad N'_k\ge\Big(\frac34\Big)^{K-k}N',\tag{4.16}$$
--   and
--   $$\varrho^\tau\le\frac{\sqrt\mu\,\eta}{C_M},\qquad\varrho^{\tau'}\le\min\Big\{\frac{\min_{s}\nu(s)}{C_P},\frac{1}{4C_{\max}+1}\Big\}.\tag{4.17}$$
--   Then $\mathbb E[(\hat\rho_K-\rho^*)^2]\le\dfrac{5\bar c^2}{N'}$, and
--   $$\mathbb E\|\Psi\hat\theta_K-\Psi\theta^*\|_D^2\le\frac1{2^K}\|\Psi\hat\theta_0-\Psi\theta^*\|_D^2+\frac{3W_1}{N}+\frac{108\bar c^2}{N'(1-\beta)^2\mu}+\frac{3\bar c^2}{4N'},\tag{4.18}$$
--   where $W_1=22\,\mathrm{trace}\{(I_d-M)^{-1}\bar\Sigma(I_d-M)^{-\top}\}+\frac{4}{\mu(1-\beta)^2}\|\bar Q^*-\Psi\theta^*\|_D^2$.
--
--   The error splits into a deterministic part that halves every epoch, the irreducible approximation error inside $W_1$, and stochastic terms of order $1/N$ and $1/N'$; with the sample-skipping lengths of order of the mixing time this gives the sample complexity of policy evaluation under Markovian noise used by the SPMD sample-complexity results.
--
--   **Formalization Note** The trajectory is a sequence of state–action random variables whose finite-dimensional laws are those of the chain $P$ from the law of $X_0$; the outputs are the deterministic functions of the trajectory given by Algorithm 3, with the sample positions described in the VRTD definition. $\rho^*$ is the average cost (2.1) at a start state $s_0$.
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
--   - encoding: θ^0 in (4.18) → the input θ̂_0 of Algorithm 3; reason: θ^0 denotes the initial point θ̂_0
--   - encoding: K, the number of epochs → K ≥ 1; reason: ρ̂_K is the output of epoch K and is undefined at K = 0
--   - encoding: ρ* = ρ^π → avgCost of π and c at a start state s₀; reason: under Assumption 1 the average cost does not depend on the start state
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 21, Theorem 4, (4.16)–(4.18); Algorithm 3 p. 20; constants pp. 19, 35–36; proof Appendix A.5, pp. 38–43

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_VRTD

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory Matrix

theorem theorem_4 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
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
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → S × A) (hX : IsSAMarkovChain μ P π X)
    (K N N' : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (η : ℝ) (hη0 : 0 < η) (T τ τ' : ℕ) (hτ : 1 ≤ τ) (hτ' : 1 ≤ τ')
    (Nk N'k : ℕ → ℕ) (θ0 : Fin d → ℝ)
    (h416 : ∀ k ∈ Finset.Icc 1 K,
      η ≤ dirichletGap P π ν Ψ / 845 ∧
      (T : ℝ) ≥ 64 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ * η) ∧
      (Nk k : ℝ) ≥ max (1160 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ ^ 2))
        ((3 / 4 : ℝ) ^ (K - k) * N) ∧
      (N'k k : ℝ) ≥ (3 / 4 : ℝ) ^ (K - k) * N')
    (h417 : ϱ ^ τ ≤ Real.sqrt (minEig (gram ν π Ψ)) * η / constCM CP P π ν Ψ ∧
      ϱ ^ τ' ≤ min ((⨅ s, ν s) / CP) (1 / (4 * constCmax CP P π ν Ψ + 1))) :
    ∫ ω, ((vrtd c Ψ η τ τ' T Nk N'k θ0 (fun j => X j ω) K).2 - avgCost P π c s₀) ^ 2 ∂μ
        ≤ 5 * cbar ^ 2 / N' ∧
    ∫ ω, dNormSq ν π (Ψ *ᵥ (vrtd c Ψ η τ τ' T Nk N'k θ0 (fun j => X j ω) K).1 - Ψ *ᵥ θstar) ∂μ
      ≤ 1 / 2 ^ K * dNormSq ν π (Ψ *ᵥ θ0 - Ψ *ᵥ θstar)
        + 3 * constW1 P π ν c Ψ θstar / N
        + 108 * cbar ^ 2 / (N' * dirichletGap P π ν Ψ ^ 2 * minEig (gram ν π Ψ))
        + 3 * cbar ^ 2 / (4 * N') := by sorry

end AvgRewardPMD.SPMD.Supplement
