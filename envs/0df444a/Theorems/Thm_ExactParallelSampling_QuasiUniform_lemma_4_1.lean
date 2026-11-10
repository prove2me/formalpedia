-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_4_1
-- name    : ExactParallelSampling.QuasiUniform.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:50.114841+00:00
-- url     : https://prove2.me/theorems/c5302b75-63b2-46d6-b09e-9ce6bfccd784
-- title:
--   Lemma 4.1 — one counting query tests independence: F is independent iff Pr[X_F = z] = ∏ 1/s_j
-- statement:
--   Let $\mu$ be quasi-uniform with known supports $\Omega_j$. For every $F\subseteq E$ and every $z\in\prod_{j\in F}\Omega_j$, the set $F$ is independent if and only if
--   $$\Pr[X_F=z]=\prod_{j\in F}\frac1{s_j}.$$
--   The supports are learned in one round of $qn$ queries $\Pr[X_j=a]$.
--
--   The one-round support-learning clause is explicit: the fixed singleton batch has size at most |E|·|α| and its answers alone determine every singleton support.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: z ∈ ∏_{j∈F} Ω_j → a full assignment z with z_j ∈ Ω_j for every j ∈ F; reason: Pr[X_F = z] reads only the values on F
--   - encoding: The supports are learned in one round of qn singleton counting queries → singletonQueries is a fixed batch of at most |E|·|α| queries; any answers agreeing on this batch recover every singleSupp through supportsFromAnswers; reason: the batch is independent of answers and the decoder has no access to the distribution; relabel each coordinate alphabet into [q] to obtain the printed qn bound
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 4.1, p. 20–21; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 4.1 (One-query independence test)**, Shen, Li, Shi and Li (2026), pp. 20–21. Let `μ`
be quasi-uniform with known supports `Ω_j`. For every `F ⊆ E` and every `z ∈ ∏_{j ∈ F} Ω_j`, the
set `F` is independent if and only if `Pr[X_F = z] = ∏_{j ∈ F} 1/s_j`. (The supports `Ω_j` are,
by definition, read off the answers `Pr[X_j = a]`.) -/
theorem lemma_4_1 {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) (F : Finset E) (z : E → α) (hz : ∀ j ∈ F, z j ∈ singleSupp p j) :
    (IsIndep p F ↔ count p F z = ∏ j ∈ F, 1 / (s p j : ℝ)) ∧
    (singletonQueries (E := E) (α := α)).card ≤ Fintype.card E * Fintype.card α ∧
    (∀ ans : (Finset E × (E → α)) → ℝ,
      (∀ Q ∈ singletonQueries (E := E) (α := α), ans Q = count p Q.1 Q.2) →
      ∀ j, supportsFromAnswers ans j = singleSupp p j) := by sorry

end ExactParallelSampling.QuasiUniform
