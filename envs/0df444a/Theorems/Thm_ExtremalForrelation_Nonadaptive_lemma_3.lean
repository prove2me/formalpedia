-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_3
-- name    : ExtremalForrelation.Nonadaptive.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:16.964192+00:00
-- url     : https://prove2.me/theorems/e852a960-eb2e-4424-b14f-1f38822947bb
-- title:
--   Lemma 3 — counting and uniformity of random half-dimensional subspaces
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Let $K$ be uniformly random among the $m$-dimensional subspaces of $\mathbb F_2^n$.
--
--   1. There are fewer than $2^{n^2/4+2}$ such subspaces.
--   2. For any fixed $t\le m$ linearly independent $v_1,\dots,v_t\in\mathbb F_2^n$,
--   $$\Pr[v_1,\dots,v_t\in K]\le M^{-t}.$$
--   3. $K^\perp$ is uniformly distributed among the $m$-dimensional subspaces as well.
--
--   Clauses 2 and 3 bound the probability that $K$ (or $K^\perp$) puts several queries in one coset (Lemma 6).
--
--   Differences from the source:
--   - encoding: K^⊥ is uniformly distributed among the m-dimensional subspaces → for every m-dimensional K₀, Pr_K[K^⊥ = K₀] = 1/#(m-dimensional subspaces); reason: this is the definition of the uniform law on that finite set
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 3, p. 9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 3 (p. 9). Let `K` be uniform among the `m`-dimensional subspaces of `𝔽₂ⁿ`, `m = n/2`.
(1) There are fewer than `2^{n²/4 + 2}` such subspaces.
(2) For fixed linearly independent `v_1, …, v_t` with `t ≤ m`, `Pr[v_1, …, v_t ∈ K] ≤ M^{−t}`.
(3) `K^⊥` is uniformly distributed among the `m`-dimensional subspaces as well. -/
theorem lemma_3 {n : ℕ} (hn : 4 ∣ n) :
    Nat.card (Grass n) < 2 ^ (n ^ 2 / 4 + 2) ∧
    (∀ t : ℕ, t ≤ n / 2 → ∀ v : Fin t → V n, LinearIndependent (ZMod 2) v →
      uprob (fun K : Grass n => ∀ ℓ, v ℓ ∈ K.1) ≤ (((2 : ℝ) ^ (n / 2))⁻¹) ^ t) ∧
    (∀ K₀ : Grass n,
      uprob (fun K : Grass n => orth K.1 = K₀.1) = 1 / (Nat.card (Grass n) : ℝ)) := by sorry

end ExtremalForrelation.Nonadaptive
