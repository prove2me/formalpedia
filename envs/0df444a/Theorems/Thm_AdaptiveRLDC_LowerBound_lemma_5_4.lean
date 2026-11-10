-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_lemma_5_4
-- name    : AdaptiveRLDC.LowerBound.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:59:42.967262+00:00
-- url     : https://prove2.me/theorems/55f3ddd1-c7fd-4822-b4fe-c555fbaffc91
-- title:
--   Lemma 5.4 — sample-based decoding from general adaptive RLDCs
-- statement:
--   Fix $\varepsilon>0$ and $\alpha,\beta\in[0,1]$ with $\alpha+\beta>1$. For every sufficiently large constant $D=D(\varepsilon,\alpha,\beta)$ and each fixed $\delta>0$, all sufficiently large binary $(q,\delta,\alpha,\beta)$-RLDCs have a sample-based decoder with per-coordinate error at most $1/3$ and
--   $$d=\left\lfloor\left(\frac\alpha{\alpha+\beta-1}+\varepsilon\right)q\right\rfloor+1,\qquad p=\min\left(1,\frac{Dq^2\log_2n}{n^{1/d}}\right).$$
--   The constant choice precedes all sizes, codes and adaptive decoders; the blocklength threshold may depend on the fixed radius. The decoder's input contains only the sampled view, including when $p=1$.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random adaptive procedures outputting 0, 1 or abort → PMF laws on published adaptive trees with Option Bool leaves; reason: tree evaluation captures arbitrary real randomness, adaptive choices, early leaves and repeated queries; this generalized item imposes no depth bound
--   - encoding: sufficiently large constant D and sufficiently large n with fixed δ,α,β,ε → ∃D₀>0 before δ and sizes, ∀D≥D₀, then ∀δ>0, ∃N≥2 before every code and decoder; reason: this records the uniform source constant and eventual threshold without fixing q or excluding p=1
--   - encoding: deterministic output from the sampled pair (W, c restricted to W) → a function on the dependent pair of a finite subset W and its Boolean assignment, with error measured by sampleWeight p; reason: the input contains exactly the observed bits and the product law is the source independent sampling law; every source decoder and sampling probability is represented
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Lemma 5.4, printed p.28, PDF p.29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_Construction

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Lemma 5.4, printed p.28 / PDF p.29: no p<1 restriction; the p=1 branch reads the full view. -/
theorem lemma_5_4 (ε α β : ℝ) (hε : 0 < ε) (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hgap : 1 < α+β) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 2 ≤ N ∧
      ∀ (k n q : ℕ), N ≤ n → 1 ≤ q →
      ∀ (C : Cube k → Cube n) (τ : Fin k → PMF (DecodeTree n)),
      IsRelaxedDecoder C q δ α β τ →
      HasSampleDecoder C (samplingRate D ε α β n q) (1/3) := by sorry

end AdaptiveRLDC.LowerBound
