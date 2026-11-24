-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_lemma_8
-- name    : AvgRewardPMD.SPMD.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:28:13.645235+00:00
-- url     : https://prove2.me/theorems/fa88fffb-7a4c-42a4-99f0-7cf477bdf5e5
-- title:
--   Lemma 8, p. 20 — for a strictly positive policy, 1 − β := inf_{x∈𝒮,‖x‖_D=1} xᵀD(I−P)x > 0 (4.11) and ⟨g(θ,ρ)−g(θ′,ρ),θ−θ′⟩ ≥ (1−β)‖Ψθ−Ψθ′‖²_D (4.12)
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying Assumptions 1 and 2, and let $\pi$ be a policy with $\pi(a\mid s)>0$ for all $s,a$. Write $P=P^\pi$ for its state–action transition matrix, $\nu$ for the stationary distribution of $P_\pi$ and $D=\mathrm{diag}(\nu(s)\pi(a\mid s))$. Let $\psi_1,\dots,\psi_d$ ($d\ge1$) be linearly independent features with $\|\psi(s,a)\|_2\le1$ for every $(s,a)$, spanning $\mathcal S=\mathrm{span}\{\psi_1,\dots,\psi_d\}$ with $\mathbf 1\notin\mathcal S$, and let $g(\theta,\rho)=\Psi^\top D(\Psi\theta-P\Psi\theta-c+\rho\mathbf 1)$ for a cost $c$. Then
--   $$1-\beta:=\inf_{x\in\mathcal S,\ \|x\|_D=1}x^\top D(I-P)x>0,\tag{4.11}$$
--   and for all $\theta,\theta'\in\mathbb R^d$ and $\rho\in\mathbb R$,
--   $$\langle g(\theta,\rho)-g(\theta',\rho),\theta-\theta'\rangle\ge(1-\beta)\|\Psi\theta-\Psi\theta'\|_D^2 .\tag{4.12}$$
--
--   The modulus $1-\beta$ plays the role of $1-\gamma$ of discounted problems: it makes the projected Bellman equation strongly monotone, which is what the convergence analysis of VRTD (Theorem 4) rests on.
--
--   **Formalization Note** $\mathcal S$ is the range $\{\Psi\theta\}$ of the feature matrix and $1-\beta$ the real infimum `dirichletGap`; $\mathbf 1\notin\mathcal S$ is "no $\theta$ has $\Psi\theta=\mathbf 1$".
--
--   Differences from the source:
--   - encoding: P = P^π, ν = ν^π → P the state–action matrix of π, ν any stationary distribution of P_π; reason: under Assumption 2 the stationary distribution is unique
--   - encoding: d linearly independent basis vectors ψ_1, …, ψ_d → d ≥ 1 and linearly independent columns of Ψ; reason: the source uses a least eigenvalue and a unit-sphere infimum, which are undefined for the zero-dimensional feature space; d ≥ 1 makes their ordinary source domain explicit
--   - encoding: π(a|s) > 0 for all s, a → π a feasible policy with π s a > 0 for all s, a; reason: the same condition; feasibility is the standing convention for policies
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 20, Lemma 8, (4.11)–(4.12); setting p. 19 (D, ψ, 𝒮, 1 ∉ 𝒮, (4.9))

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_VRTD

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning Matrix

theorem lemma_8 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (herg : IsErgodic P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (hπpos : ∀ s a, 0 < π s a)
    (ν : S → ℝ) (hν : MarkovMixing.IsStationary (stateMatrix P π) ν)
    (c : S → A → ℝ) (d : ℕ) (hd : 0 < d) (Ψ : Matrix (S × A) (Fin d) ℝ)
    (hlin : LinearIndependent ℝ Ψᵀ) (hfeat : ∀ x, ∑ i, Ψ x i ^ 2 ≤ 1)
    (hone : ∀ θ : Fin d → ℝ, Ψ *ᵥ θ ≠ fun _ => 1) :
    0 < dirichletGap P π ν Ψ ∧
      ∀ (θ θ' : Fin d → ℝ) (ρ : ℝ),
        dirichletGap P π ν Ψ * dNormSq ν π (Ψ *ᵥ θ - Ψ *ᵥ θ')
          ≤ (opG P π ν c Ψ θ ρ - opG P π ν c Ψ θ' ρ) ⬝ᵥ (θ - θ') := by sorry

end AvgRewardPMD.SPMD.Supplement
