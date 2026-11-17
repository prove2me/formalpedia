-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_7_3
-- name    : CosDensity.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:22:15.545207+00:00
-- url     : https://prove2.me/theorems/eb972959-ec7f-4eba-a5f7-ae3f56246270
-- title:
--   Theorem 7.3 — real higher moments in $\widetilde O_p(d^{p/2}\epsilon^{-4+4/p}\log(1/\delta))$ words
-- statement:
--   For every fixed real $p>2$ there is a constant $C_p>0$ such that, for every $0<\epsilon,\delta<1$, Algorithm 2 gives a one-pass $(1+\epsilon)$-approximation to $M_p(P)$ with probability at least $1-\delta$ on every nonempty nonnegative-cosine stream in $\mathbb R^d$.
--
--   Quantitatively, put
--   $$\theta=C_p d^{p/2}/\epsilon^2,\qquad K=\lceil4\theta\rceil.$$
--   The number of scalar counters is bounded by a constant times the two terms of Equation (18),
--   $$K^{1-2/p}\epsilon^{-2}+K^{1-2/p}\epsilon^{-4/p}\log_2(\max\{2,K\}),$$
--   each counter is lifted to $d$ words, and $O(\log(1/\delta))$ independent copies are used for median amplification. Successful runs do not overflow.
--
--   Differences from the source:
--   - encoding: $\widetilde O_p(d^{p/2}\epsilon^{-4+4/p}\log(1/\delta))$ words → a constant $C_p$, the printed $\theta$ and $K=\lceil4\theta\rceil$, both terms of (18), the $d$-fold lift, and an explicit ceiling for median repetitions; reason: these are exactly the proof-explicit factors hidden by the tilde notation
--   - encoding: Algorithm 2 may return `OVERFLOW` → successful seeds return `some estimate`; reason: the success event records both absence of overflow and the approximation guarantee
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Equation (18), Algorithm 2 and Theorem 7.3, pp.25–28 (PDF pp.26–29)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Supplement_realMoment
import Definitions.Def_CosDensity_Supplement_WordStreamAlg

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Equation (18), Algorithm 2 and
Theorem 7.3, pp.25–28 (PDF pp.26–29).

For every fixed real `p > 2`, `C` fixes all constants hidden by the printed `tilde-O_p`.
Here `theta = C d^(p/2)/epsilon²`, `K = ceil(4 theta)`, `counters` is the two-term
linear-`F_p` sketch bound from (18), and `repetitions` is the median amplification factor.
The success event includes the absence of the explicit `OVERFLOW` outcome. -/
theorem theorem_7_3 :
    ∀ p : ℝ, 2 < p → ∃ C : ℝ, 0 < C ∧
      ∀ (epsilon delta : ℝ), 0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ∀ (d n : ℕ), 0 < n →
        let theta : ℝ := C * (d : ℝ) ^ (p / 2) / epsilon ^ 2
        let K : ℕ := Nat.ceil (4 * theta)
        let counters : ℝ := C *
          (((K : ℝ) ^ (1 - 2 / p)) / epsilon ^ 2 +
            ((K : ℝ) ^ (1 - 2 / p)) / (epsilon ^ (4 / p)) *
              Real.logb 2 (max 2 K))
        let repetitions : ℕ := Nat.ceil (C * Real.logb 2 (2 / delta))
        ∃ A : WordStreamAlg (EuclideanSpace ℝ (Fin d)),
          A.words ≤ repetitions * Nat.ceil (d * counters + d) ∧
          ∀ P : List (EuclideanSpace ℝ (Fin d)),
            P.length = n → (∀ x ∈ P, x ≠ 0) → CosDensity.NonnegCosine P →
            A.Succeeds (fun omega => ∃ estimate : ℝ,
              A.estimate omega P = some estimate ∧
                CosDensity.IsApprox epsilon (realMoment p P) estimate)
              (ENNReal.ofReal (1 - delta)) := by sorry

end CosDensity.Supplement
