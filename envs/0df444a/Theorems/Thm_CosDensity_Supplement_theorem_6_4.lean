-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_6_4
-- name    : CosDensity.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:21:14.0921+00:00
-- url     : https://prove2.me/theorems/dfc15933-f261-4c40-b89c-850a243416ed
-- title:
--   Theorem 6.4 — approximating $M_2$ needs $\Omega(d)$ bits
-- statement:
--   Fix $0<\epsilon<1/5$. There are constants $c>0$, $C$, $K$, and $d_0$ such that, for every $d\ge d_0$, any one-pass algorithm that $(1+\epsilon)$-approximates $M_2$ with probability at least $2/3$ on every nonempty stream of nonzero vectors with nonnegative pairwise cosine, length at most $Cd$, and rational coordinates of height at most $d^K$, satisfies
--   $$\log_2|S|\ge c d.$$
--
--   Differences from the source:
--   - encoding: $\Omega(d)$ bits, $O(d)$ length, and $O(\log d)$-bit coordinates → constants $c,C,K,d_0$, length $\le Cd$, coordinate height $\le d^K$, and memory $\log_2|S|$; reason: this is the quantified content of the theorem's asymptotic clauses
--   - encoding: the lower bound holds even in the nonnegative-cosine regime → correctness is required only on the stated nonzero, nonnegative-cosine finite-precision class; reason: this expresses the theorem's promise clause in the paper's normalize-on-arrival model
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.4, pp.22–23 (PDF pp.23–24)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 6.4, p.22 (PDF p.23).

For fixed `epsilon < 1/5`, correctness only on nonzero, nonnegative-cosine streams of linear length,
with polynomially bounded rational coordinate height, forces linear bit memory. -/
theorem theorem_6_4 :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 5 →
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 0 < C ∧ ∃ K d₀ : ℕ, ∀ d ≥ d₀,
        ∀ (S Omega : Type) [Fintype S] [Nonempty S] [MeasurableSpace Omega]
          (mu : Measure Omega) [IsProbabilityMeasure mu]
          (A : CosDensity.StreamAlg (EuclideanSpace ℝ (Fin d)) Omega S),
          (∀ P : List (EuclideanSpace ℝ (Fin d)),
            P ≠ [] → (∀ x ∈ P, x ≠ 0) → CosDensity.NonnegCosine P →
            P.length ≤ C * d → CosDensity.IsBitBounded (d ^ K) P →
            CosDensity.SucceedsWP mu (fun omega =>
              CosDensity.IsApprox epsilon (CosDensity.moment 2 P) (A.estimate omega P))
              (2 / 3 : ENNReal)) →
          c * d ≤ CosDensity.memoryBits S := by sorry

end CosDensity.Supplement
