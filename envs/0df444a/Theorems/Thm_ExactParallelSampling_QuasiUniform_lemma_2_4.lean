-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_2_4
-- name    : ExactParallelSampling.QuasiUniform.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:57.316409+00:00
-- url     : https://prove2.me/theorems/5031ddd4-fac6-4553-922c-505aff4e40f2
-- title:
--   Lemma 2.4 — marginals and conditional laws of a quasi-uniform distribution are quasi-uniform; conditional support sizes are integers and monotone
-- statement:
--   Let $\mu$ be a quasi-uniform distribution on $\Sigma^E$.
--
--   (a) For every $K\subseteq E$ the law of $X_K$ is quasi-uniform. Its supports are those of $\mu$: for every $S\subseteq K$ the law of $X_K$ has $|\Omega_S|$ support points on $S$, and a pinning of $S$ has positive probability under it iff it has under $\mu$.
--
--   (b) For every $K\subseteq E$ and $y\in\Omega_K$, the conditional law of $X_{E\setminus K}$ given $X_K=y$ is quasi-uniform. For every $T\subseteq E\setminus K$ its marginal on $T$ is uniform on a set of $|\Omega_{K\cup T}|/|\Omega_K|$ elements. In particular, for $j\notin K$ the coordinate $X_j$ takes exactly $s_K(j)$ values given $X_K=y$, so $s_K(j)$ is a positive integer that does not depend on $y$.
--
--   (c) If $S\subseteq S'\subseteq E$ and $j\in E\setminus S'$, then $s_{S'}(j)\le s_S(j)$.
--
--   Differences from the source:
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: the law of X_K "with supports Ω_S for S ⊆ K" → marg p K on restrictions ↥K → α; for every S : Finset ↥K, its support size on S equals |Ω_S| of μ (S mapped into E), and a pinning has positive probability under it iff under μ; reason: subsets of K are finsets of the subtype ↥K; having the same supports means the same positive pinnings, hence the same cardinalities
--   - encoding: conditional law of X_{E∖K} given X_K = y, y ∈ Ω_K → condLaw p K y on assignments of the subtype {j // j ∉ K}, at y ∈ supp p K; reason: this is the conditional law at a consistent pinning
--   - encoding: s_K(j) is a positive integer that does not depend on y → ∃ t : ℕ, 0 < t, condSize p K j = t, and the conditional law's s at j equals t (for every y ∈ Ω_K); reason: condSize is computed from μ alone, so the same t serves every y
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 2.4, p. 13; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 2.4 (Basic facts)**, Shen, Li, Shi and Li (2026), p. 13. Let `μ` be quasi-uniform.
(a) For every `K ⊆ E` the law of `X_K` is quasi-uniform, with supports `Ω_S` for `S ⊆ K`.
(b) For every `K ⊆ E` and `y ∈ Ω_K` the conditional law of `X_{E∖K}` given `X_K = y` is
quasi-uniform, and for `T ⊆ E ∖ K` its marginal on `T` is uniform on a set of `|Ω_{K∪T}|/|Ω_K|`
elements; in particular, for `j ∉ K`, `X_j` takes exactly `s_K(j)` values given `X_K = y`, so
`s_K(j)` is a positive integer that does not depend on `y`.
(c) If `S ⊆ S' ⊆ E` and `j ∈ E ∖ S'`, then `s_{S'}(j) ≤ s_S(j)`. -/
theorem lemma_2_4 {E α : Type*} [Fintype E] [Fintype α] (p : (E → α) → ℝ)
    (hp : IsQuasiUniform p) :
    -- (a)
    (∀ K : Finset E, IsQuasiUniform (marg p K) ∧
      ∀ S : Finset ↥K,
        suppCard (marg p K) S = suppCard p (S.map (Function.Embedding.subtype _)) ∧
        ∀ x : E → α, (0 < count (marg p K) S (K.restrict x) ↔
          0 < count p (S.map (Function.Embedding.subtype _)) x)) ∧
    -- (b)
    (∀ K : Finset E, ∀ y ∈ supp p K,
      IsQuasiUniform (condLaw p K y) ∧
      (∀ T : Finset {j // j ∉ K},
        (suppCard (condLaw p K y) T : ℝ) =
            (suppCard p (K ∪ T.map (Function.Embedding.subtype _)) : ℝ) / (suppCard p K : ℝ) ∧
        ∀ w ∈ supp (condLaw p K y) T,
          marg (condLaw p K y) T w = 1 / (suppCard (condLaw p K y) T : ℝ)) ∧
      ∀ j (hj : j ∉ K), ∃ t : ℕ, 0 < t ∧ condSize p K j = (t : ℝ) ∧
        s (condLaw p K y) ⟨j, hj⟩ = t) ∧
    -- (c)
    (∀ S S' : Finset E, S ⊆ S' → ∀ j, j ∉ S' → condSize p S' j ≤ condSize p S j) := by sorry

end ExactParallelSampling.QuasiUniform
