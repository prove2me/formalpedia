-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_6_4
-- name    : ExactParallelSampling.QuasiUniform.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:52:02.101965+00:00
-- url     : https://prove2.me/theorems/9327fc13-c2c2-457a-8264-74d51c6a5a90
-- title:
--   Lemma 6.4 — hypergeometric point bound Pr[Z = z] ≥ 2^{−6ξ}/(5√max(z,1))
-- statement:
--   Let $Z$ be the number of marked elements in a uniformly random $\ell$-subset of an $m$-element set containing $b$ marked elements, with $1\le b\le m/2$ and $1\le\ell\le m/2$, and let $\bar z=\ell b/m$. For every $\xi>0$ and every integer $z$ with $0\le z\le\min(b,\ell)$ and $(z-\bar z)^2\le\xi\bar z$,
--   $$\Pr[Z=z]\ge\frac{2^{-6\xi}}{5\sqrt{\max(z,1)}}.$$
--
--   Differences from the source:
--   - encoding: an m-element set containing b marked elements; an integer z ≥ 0 → Fin m with an arbitrary marked subset of size b; z : ℕ; reason: relabelling; the law of Z depends only on m, b, ℓ
--   - encoding: probabilities over uniformly random finite objects → uprob: the number of favourable outcomes divided by the number of outcomes; reason: this is the uniform distribution on a finite set
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 6.4, p. 31; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 6.4 (Hypergeometric point bound)**, Shen, Li, Shi and Li (2026), p. 31. Let `Z` be the
number of marked elements in a uniformly random `ℓ`-subset of an `m`-element set containing `b`
marked elements, with `1 ≤ b ≤ m/2` and `1 ≤ ℓ ≤ m/2`, and let `z̄ = ℓb/m`. For every `ξ > 0` and
every integer `z` with `0 ≤ z ≤ min(b, ℓ)` and `(z − z̄)² ≤ ξ z̄`,
`Pr[Z = z] ≥ 2^{−6ξ} / (5 √max(z, 1))`. -/
theorem lemma_6_4 (m b ℓ : ℕ) (marked : Finset (Fin m)) (hb : marked.card = b) (hb1 : 1 ≤ b)
    (hb2 : (b : ℝ) ≤ (m : ℝ) / 2) (hl1 : 1 ≤ ℓ) (hl2 : (ℓ : ℝ) ≤ (m : ℝ) / 2) (ξ : ℝ)
    (hξ : 0 < ξ) (z : ℕ) (hz : z ≤ min b ℓ)
    (hdev : ((z : ℝ) - (ℓ : ℝ) * b / m) ^ 2 ≤ ξ * ((ℓ : ℝ) * b / m)) :
    (2 : ℝ) ^ (-6 * ξ) / (5 * Real.sqrt (max (z : ℝ) 1)) ≤
      uprob {T // T ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ}
        (fun T => (T.1 ∩ marked).card = z) := by sorry

end ExactParallelSampling.QuasiUniform
