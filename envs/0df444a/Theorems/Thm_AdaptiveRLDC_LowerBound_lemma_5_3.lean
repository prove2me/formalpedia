-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_lemma_5_3
-- name    : AdaptiveRLDC.LowerBound.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:57:07.179197+00:00
-- url     : https://prove2.me/theorems/ed5d578a-e564-4530-9772-eefd9f3bbb1c
-- title:
--   Lemma 5.3 — exact coordinate-wise entropy lower bound
-- statement:
--   Let $e\in(0,1/2)$ be fixed. The coefficient $1-h_2(e)$ is positive, and every binary code $C:\{0,1\}^k\to\{0,1\}^n$ with a sample-based decoder of sampling probability $p\in(0,1]$ and per-coordinate error at most $e$ satisfies
--   $$pn\ge(1-h_2(e))k.$$
--   Here $h_2$ is the published binary entropy in bits. Positivity is asserted before quantifying over sizes, codes and sampling probabilities, so the final clause also expresses the uniform $pn=\Omega(k)$ consequence. Only coordinate-wise success is required.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: the exact entropy inequality and its fixed-error Ω(k) consequence → positivity of the exact coefficient followed by the inequality for every size, code and sampling rate; reason: the same coefficient is an explicit uniform Ω constant; error e lies in the source domain (0,1/2)
--   - encoding: deterministic output from the sampled pair (W, c restricted to W) → a function on the dependent pair of a finite subset W and its Boolean assignment, with error measured by sampleWeight p; reason: the input contains exactly the observed bits and the product law is the source independent sampling law; every source decoder and sampling probability is represented
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Lemma 5.3, printed p.27, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SampleDecoder
import Definitions.Def_AdaptiveRLDC_LowerBound_Entropy

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Lemma 5.3, printed p.27 / PDF p.28: exact entropy coefficient, whose positivity
also states the constant-error Ω(k) consequence uniformly before all sizes and codes. -/
theorem lemma_5_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1/2) :
    0 < 1 - WildeQIT.binaryEntropy ε ∧
    ∀ {k n : ℕ} (C : Cube k → Cube n) (p : ℝ), HasSampleDecoder C p ε →
      (1 - WildeQIT.binaryEntropy ε) * (k : ℝ) ≤ p * (n : ℝ) := by sorry

end AdaptiveRLDC.LowerBound
