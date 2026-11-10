-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_theorem_4_12
-- name    : AdaptiveRLDC.LowerBound.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:57:18.488201+00:00
-- url     : https://prove2.me/theorems/02485283-dea1-4278-a5da-8ff07de45367
-- title:
--   Theorem 4.12 — general self-bounding lower tail
-- statement:
--   Let $X$ have independent binary coordinates with arbitrary parameters $\pi_i\in[0,1]$, and let $f$ be nonnegative and strongly $(a,0)$-self-bounding, where $a\ge1/3$. Write $Z=f(X)$. For $0<t\le\mathbb EZ$,
--   $$\Pr[Z\le\mathbb EZ-t]\le\exp\left(-\frac{t^2}{2a\mathbb EZ}\right).$$
--   This is the entire source lower-tail range, including its endpoint in $t$.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random binary vectors and their expectations and event probabilities → exact finite sums under their joint weights, with product weights for independent coordinates; reason: every law on the finite binary cube is represented; independent coordinates may have distinct arbitrary real probabilities
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Theorem 4.12, printed p.21, PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SelfBounding

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Theorem 4.12, printed p.21 / PDF p.22: the full a≥1/3 range and non-strict event. -/
theorem theorem_4_12 {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (f : Cube n → ℝ) (a : ℝ) (ha : 1/3 ≤ a) (hf : StronglySelfBounding f a 0)
    (t : ℝ) (ht : 0 < t) (htμ : t ≤ mean (productWeight π) f) :
    eventMass (productWeight π) (fun x => f x ≤ mean (productWeight π) f - t) ≤
      Real.exp (-(t^2) / (2*a*mean (productWeight π) f)) := by sorry

end AdaptiveRLDC.LowerBound
