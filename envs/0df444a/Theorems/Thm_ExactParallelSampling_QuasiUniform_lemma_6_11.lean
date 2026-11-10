-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_6_11
-- name    : ExactParallelSampling.QuasiUniform.lemma_6_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:52:17.50881+00:00
-- url     : https://prove2.me/theorems/c5b64fb0-163f-4581-a0b4-02e9c07fd1bc
-- title:
--   Lemma 6.11 — some run among R_c = ⌈2^{24}n⌉ runs of Certify(S) certifies ≥ 2^{−24}|S|/log n elements, w.p. ≥ 1 − 2^{−n}
-- statement:
--   Standing assumptions of §6: $I$ is an independence system with (A1) on a ground set $E$ of $n\ge n_0(\gamma)$ elements, $\gamma\in(0,1]$.
--
--   Let $S$ be dependent, with $\alpha(S)\le|S|/(100\log n)$ and $p_x(S)\ge n^{-2-\gamma}/4$ for every $x\in S$. Then, with probability at least $1-2^{-n}$, at least one of $R_c=\lceil2^{24}n\rceil$ independent runs of Certify$(S)$ returns a set $R$ with $|R|\ge c_1|S|/\log n$, where $c_1=2^{-24}$.
--
--   Each run of Certify draws a uniformly random $m_S$-subset $S'$ of $S$ and $N_c$ uniformly random orders of $S'$. It returns $R=\{x\in S\setminus S':Q_\sigma+x\notin I\text{ for some }\sigma\}$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §6: I an independence system on E, |E| = n, (A1) every singleton independent → SubsamplingSM.Offline.IsIndepSystem I (∅ ∈ I, downward closed; no exchange axiom) and ∀ x, I {x}; E a finite type with n = Fintype.card E; reason: the published predicate is exactly the definition of an independence system
--   - encoding: n ≥ n₀(γ), where n₀(γ) ≥ 2^{34/γ} also exceeds a sufficiently large absolute constant → ∃ n₀ (chosen after γ), ∀ ground sets with n ≥ n₀; reason: the source leaves the threshold unspecified beyond being sufficiently large, so it is an existential threshold depending only on γ
--   - encoding: R_c independent runs of Certify(S), each drawing a uniform m_S-subset S′ and N_c independent uniform orders of S′ → the uniform distribution on Fin R_c → CertRand n γ S, where CertRand is the dependent pair (S′, orders of S′); reason: every S′ has the same number of order tuples, so the uniform distribution on the pairs is S′ uniform followed by uniform orders; independent runs are the product
--   - encoding: Certify uses two rounds (prefix queries, then the queries Q_σ + x) → certifyR is defined from those queries' answers; reason: the round structure is the definition of Algorithm 4
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 6.11, p. 35; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 6.11 (Certification, after [KPS26a, Theorem 6.3])**, Shen, Li, Shi and Li (2026),
p. 35. Standing assumptions of §6 (independence system with (A1), `|E| = n ≥ n₀(γ)`). Let `S` be
dependent with `α(S) ≤ |S|/(100 log n)` and `p_x(S) ≥ n^{−2−γ}/4` for every `x ∈ S`. With
probability at least `1 − 2^{−n}`, at least one of `R_c = ⌈2^{24} n⌉` independent runs of
Certify(S) returns a set `R` with `|R| ≥ c₁|S|/log n`, where `c₁ = 2^{−24}`. -/
theorem lemma_6_11 : ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ n0 : ℕ,
    ∀ {E : Type} [Fintype E] [LinearOrder E], n0 ≤ Fintype.card E →
    ∀ I : Finset E → Prop, SubsamplingSM.Offline.IsIndepSystem I → (∀ x, I {x}) →
    ∀ S : Finset E, ¬ I S →
      (alphaVal I S : ℝ) ≤ (S.card : ℝ) / (100 * Real.logb 2 (Fintype.card E)) →
      (∀ x ∈ S, (Fintype.card E : ℝ) ^ (-2 - γ) / 4 ≤ essProb I S x) →
      1 - (2 : ℝ) ^ (-(Fintype.card E : ℝ)) ≤
        uprob (Fin (Rcert (Fintype.card E)) → CertRand (Fintype.card E) γ S) (fun c =>
          ∃ k, (2 : ℝ) ^ (-24 : ℤ) * S.card / Real.logb 2 (Fintype.card E) ≤
            ((certifyR I (c k)).card : ℝ)) := by sorry

end ExactParallelSampling.QuasiUniform
