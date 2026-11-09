-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_9
-- name    : ExtremalForrelation.Nonadaptive.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:28.034807+00:00
-- url     : https://prove2.me/theorems/7f134caa-f139-4fcb-998a-667e7607845d
-- title:
--   Lemma 9 — the likelihood ratio is controlled by matching probabilities
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a subspace $K$ with $\dim K=m$ and a query set $Q$. For every $s\in\mathbb F_2$,
--   $$\mathbb E_{\tau\sim\rho(\cdot\mid K)}\big|L_s(\tau)-1\big|\le\Big(\mathbb E_{\tau\sim\rho(\cdot\mid K)}\sum_{\substack{I\subseteq F,\ J\subseteq G\\ |I|=|J|\ge1}}p_{I,J}(H_\tau)^2\Big)^{1/2}.$$
--
--   Through equation (14), this bounds $\|\mu_s(\cdot\mid K)-\rho(\cdot\mid K)\|_{TV}$ by the matching probabilities of the pinning graph alone.
--
--   Differences from the source:
--   - encoding: E_{τ∼ρ(·|K)} X(τ), with L_s defined where ρ(τ | K) > 0 → ∑_τ ρ(τ | K) X(τ), with L_s = μ_s(τ | K)/ρ(τ | K) everywhere; reason: transcripts with ρ(τ | K) = 0 carry weight 0, so the value of L_s and of p_{I,J} there does not matter
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 9, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 9 (p. 16). For every `s`,
`E_{τ∼ρ(·|K)} |L_s(τ) − 1| ≤ (E_{τ∼ρ(·|K)} ∑_{I ⊆ F, J ⊆ G, |I| = |J| ≥ 1} p_{I,J}(H_τ)²)^{1/2}`.
Expectations under `ρ(· | K)` are the sums `∑_τ ρ(τ | K) X(τ)`; transcripts with
`ρ(τ | K) = 0` carry weight `0`. -/
theorem lemma_9 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (s : ZMod 2) :
    ∑ τ : Transcript Q, rhoK Q K τ * |Lratio Q K s τ - 1| ≤
      Real.sqrt (∑ τ : Transcript Q, rhoK Q K τ * sumSqMatchProb Q K (pinGraph Q K τ)) := by sorry

end ExtremalForrelation.Nonadaptive
