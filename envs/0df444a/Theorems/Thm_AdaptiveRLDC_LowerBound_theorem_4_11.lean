-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_theorem_4_11
-- name    : AdaptiveRLDC.LowerBound.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:57:05.440493+00:00
-- url     : https://prove2.me/theorems/a93b12de-e54e-416d-9249-215041e2d86e
-- title:
--   Theorem 4.11 — general self-bounding upper tail
-- statement:
--   Let $X$ have independent binary coordinates with arbitrary parameters $\pi_i\in[0,1]$, let $a>0$, and let $f$ be nonnegative and strongly $(a,0)$-self-bounding. Write $Z=f(X)$. For every $t>0$,
--   $$\Pr[Z\ge\mathbb EZ+t]\le\exp\left(-\frac{t^2}{2a\mathbb EZ+at}\right).$$
--   The parameters need not be identical. This target retains every positive $a$ and the non-strict tail event.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random binary vectors and their expectations and event probabilities → exact finite sums under their joint weights, with product weights for independent coordinates; reason: every law on the finite binary cube is represented; independent coordinates may have distinct arbitrary real probabilities
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Theorem 4.11, printed p.21, PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SelfBounding

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Theorem 4.11, printed p.21 / PDF p.22: independent coordinates, not necessarily identical. -/
theorem theorem_4_11 {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (f : Cube n → ℝ) (a : ℝ) (ha : 0 < a) (hf : StronglySelfBounding f a 0)
    (t : ℝ) (ht : 0 < t) :
    eventMass (productWeight π) (fun x => mean (productWeight π) f + t ≤ f x) ≤
      Real.exp (-(t^2) / (2*a*mean (productWeight π) f + a*t)) := by sorry

end AdaptiveRLDC.LowerBound
