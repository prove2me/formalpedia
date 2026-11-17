-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_5_2
-- name    : CosDensity.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:19:33.217125+00:00
-- url     : https://prove2.me/theorems/ecb6908b-7d69-41e5-9d94-407579fc356b
-- title:
--   Theorem 5.2 — one-pass diversity-index estimator
-- statement:
--   Let $0<\epsilon,\delta<1$, and let $P$ be a nonempty stream of $n$ nonzero vectors in $\mathbb R^d$ with pairwise nonnegative cosine similarities. Set
--   $$\lambda=\frac{8}{3\epsilon^2}\ln\frac4\delta$$
--   and let $N_{\max}$ be the ceiling of
--   $$\lambda d+\sqrt{2\lambda d\ln(2n/\delta)}+\frac23\ln(2n/\delta).$$
--   There is a one-pass rejection-sampling algorithm using at most
--   $$d+(d+2)N_{\max}+4$$
--   real words that, with probability at least $1-\delta$, does not overflow and returns a $(1+\epsilon)$-approximation to $M_{-1}(P)$.
--
--   Differences from the source:
--   - encoding: $O(d^2\epsilon^{-2}\log(1/\delta)+d\log(n/\delta))$ words → the explicit Algorithm 1 cap $d+(d+2)N_{\max}+4$ with the printed $\lambda$ and $N_{\max}$; reason: multiplying the maximum retained tuples by their $d+2$ stored scalars gives the displayed asymptotic bound
--   - encoding: Algorithm 1 returns `OVERFLOW` on cap violation → successful seeds have an output `some estimate`; reason: this simultaneously records no overflow and the approximation event
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Algorithm 1 and Theorem 5.2, pp.16–17 (PDF pp.17–18)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Supplement_diversityIndex
import Definitions.Def_CosDensity_Supplement_WordStreamAlg

open scoped RealInnerProductSpace

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Algorithm 1 and Theorem 5.2,
pp.16–17 (PDF pp.17–18).

The rejection-sampling diversity estimator uses the paper's explicit `lambda` and `Nmax`. With
probability at least `1-delta` it neither overflows nor fails the `(1+epsilon)` guarantee. The word
bound counts the vector sum and, for every retained sample, its `d` coordinates, random threshold,
and current density. -/
theorem theorem_5_2 :
    ∀ (epsilon delta : ℝ), 0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ∀ (d n : ℕ), 0 < n →
        let lambda : ℝ := 8 / (3 * epsilon ^ 2) * Real.log (4 / delta)
        let Nmax : ℕ := Nat.ceil
          (lambda * d + Real.sqrt (2 * lambda * d * Real.log (2 * n / delta)) +
            (2 / 3 : ℝ) * Real.log (2 * n / delta))
        ∃ A : WordStreamAlg (EuclideanSpace ℝ (Fin d)),
          A.words ≤ d + (d + 2) * Nmax + 4 ∧
          ∀ P : List (EuclideanSpace ℝ (Fin d)),
            P.length = n → (∀ x ∈ P, x ≠ 0) → CosDensity.NonnegCosine P →
            A.Succeeds (fun omega => ∃ estimate : ℝ,
              A.estimate omega P = some estimate ∧
                CosDensity.IsApprox epsilon (diversityIndex P) estimate)
              (ENNReal.ofReal (1 - delta)) := by sorry

end CosDensity.Supplement
