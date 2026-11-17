-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_6_6
-- name    : CosDensity.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:21:38.800376+00:00
-- url     : https://prove2.me/theorems/a043adea-fde8-4c66-9157-94328b56d021
-- title:
--   Theorem 6.6 — higher even moments need $\widetilde\Omega_{p,\epsilon}(d^{p/2})$ bits
-- statement:
--   Fix an even integer $p\ge4$ and $0<\epsilon<1$. There exist $c>0$, a length constant $C$, a precision exponent $K$, and $d_0$ such that, for every $d\ge d_0$, any one-pass algorithm that $(1+\epsilon)$-approximates $M_p$ with probability at least $2/3$ on every nonempty stream of nonzero vectors of length at most $C d^{p/2}$ and rational coordinate height at most $d^K$ satisfies
--   $$\log_2|S|\ge c\frac{d^{p/2}}{(\log_2 d)^{p/2}}.$$
--   No cosine-sign promise is imposed.
--
--   Differences from the source:
--   - encoding: $\Omega_{p,\epsilon}(d^{p/2}/(\log d)^{p/2})$ bits → constants $c,d_0$ chosen after $(p,\epsilon)$ and before $d$, with the displayed base-two logarithm and memory $\log_2|S|$; reason: this is the quantified meaning of the printed lower bound
--   - generalization: stream length $\widetilde O_p(d^{p/2})$ and $O(\log d)$-bit rationals → length $\le C d^{p/2}$ and coordinate height $\le d^K$ for constants fixed before $d$; reason: the proof gives $2R+m=O_{p,\epsilon}(d^{p/2})$, so the Lean promise is stronger and every source algorithm specializes to it
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.6, pp.23–25 (PDF pp.24–26)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.6, p.23 (PDF p.24),
with the quantitative reduction on pp.23–25.

For fixed even `p ≥ 4` and fixed `epsilon`, the constants in the `Omega`, stream-length, and
coordinate-precision bounds precede the dimension and algorithm. The promise has no cosine-sign
restriction. -/
theorem theorem_6_6 :
    ∀ p : ℕ, 4 ≤ p → Even p → ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 0 < C ∧ ∃ K d₀ : ℕ, ∀ d ≥ d₀,
        ∀ (S Omega : Type) [Fintype S] [Nonempty S] [MeasurableSpace Omega]
          (mu : Measure Omega) [IsProbabilityMeasure mu]
          (A : CosDensity.StreamAlg (EuclideanSpace ℝ (Fin d)) Omega S),
          (∀ P : List (EuclideanSpace ℝ (Fin d)),
            P ≠ [] → (∀ x ∈ P, x ≠ 0) →
            P.length ≤ C * d ^ (p / 2) → CosDensity.IsBitBounded (d ^ K) P →
            CosDensity.SucceedsWP mu (fun omega =>
              CosDensity.IsApprox epsilon (CosDensity.moment p P) (A.estimate omega P))
              (2 / 3 : ENNReal)) →
          c * ((d : ℝ) ^ (p / 2) / (Real.logb 2 d) ^ (p / 2)) ≤
            CosDensity.memoryBits S := by sorry

end CosDensity.Supplement
