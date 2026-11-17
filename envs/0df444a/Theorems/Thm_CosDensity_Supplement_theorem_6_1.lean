-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_6_1
-- name    : CosDensity.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:20:46.06952+00:00
-- url     : https://prove2.me/theorems/5491406c-4c3b-4c21-8ad3-298c82af0035
-- title:
--   Theorem 6.1 — lifted AMS estimator for even density moments
-- statement:
--   There is an absolute constant $C>0$ such that, for every integer $k\ge1$, every $0<\epsilon,\delta<1$, and every stream $P$ in $\mathbb R^d$, a one-pass algorithm returns a $(1+\epsilon)$-approximation to $M_{2k}(P)$ with probability at least $1-\delta$ using at most
--   $$\left\lceil C\binom{d+k-1}{k}\epsilon^{-2}\log_2(2/\delta)+d\right\rceil$$
--   real words.
--
--   Differences from the source:
--   - generalization: input vectors are nonzero by the paper's standing convention → the lifted AMS statement also covers zero vectors under $\operatorname{unitize}(0)=0$; reason: the tensor identity and AMS estimate remain valid and specialize to the source
--   - encoding: $O(\binom{d+k-1}{k}\epsilon^{-2}\log(1/\delta))$ words → one algorithm for all stream lengths, with an absolute $C$, the displayed $\log_2(2/\delta)$ ceiling, and the shared $d$-word sum; reason: the proof uses one constant-success group plus median amplification, and $\log_2(2/\delta)=1+\log_2(1/\delta)$ quantifies the printed bound uniformly for every $\delta\in(0,1)$
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.1, pp.20–21 (PDF pp.21–22)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Supplement_WordStreamAlg

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.1, p.20 (PDF p.21),
with the normalized monomial map and AMS calculation on pp.20–21.

One absolute constant controls the number of independent lifted AMS counters. The state bound
retains the exact lifted dimension `choose (d+k-1) k`, the `epsilon⁻²` averaging factor, the
base-two logarithmic median-amplification factor, and the shared `d`-word vector sum. The factor
`log₂(2/delta) = 1 + log₂(1/delta)` includes the one constant-success group needed before
amplification. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ (epsilon delta : ℝ), 0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ∀ d : ℕ,
        ∃ A : WordStreamAlg (EuclideanSpace ℝ (Fin d)),
          A.words ≤ Nat.ceil
            (C * (Nat.choose (d + k - 1) k : ℝ) / epsilon ^ 2 * Real.logb 2 (2 / delta) + d) ∧
          ∀ P : List (EuclideanSpace ℝ (Fin d)),
            A.Succeeds (fun omega => ∃ estimate : ℝ,
              A.estimate omega P = some estimate ∧
                CosDensity.IsApprox epsilon (CosDensity.moment (2 * k) P) estimate)
              (ENNReal.ofReal (1 - delta)) := by sorry

end CosDensity.Supplement
