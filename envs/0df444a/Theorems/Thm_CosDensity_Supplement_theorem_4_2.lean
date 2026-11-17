-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_4_2
-- name    : CosDensity.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:18:22.165211+00:00
-- url     : https://prove2.me/theorems/298e87b9-d810-4ed8-9fda-0f752448be57
-- title:
--   Theorem 4.2 — exact $M_1$ computation needs $\Omega(d)$ bits
-- statement:
--   There are absolute constants $c>0$ and $d_0$ such that, for every $d\ge d_0$, any randomized one-pass finite-state algorithm that computes $M_1(P)$ exactly with probability at least $2/3$ on every stream of at most $d+1$ standard basis vectors in $\mathbb R^d$ satisfies
--   $$\log_2|S|\ge c d,$$
--   where $S$ is its memory-state set.
--
--   Thus the linear lower bound already holds on $O(d)$-length nonnegative-cosine streams.
--
--   Differences from the source:
--   - encoding: $\Omega(d)$ bits on $O(d)$-length standard-basis streams → constants $c>0,d_0$ and the explicit promise $|P|\le d+1$, with memory $\log_2|S|$; reason: this is the quantified meaning supplied by the INDEX reduction with $m=\lfloor d/2\rfloor$
--   - encoding: success probability at least $2/3$ → an inner-probability event of measure at least $2/3$ in the persistent-seed model; reason: measurable inner witnesses retain the paper's guarantee and support the one-way reduction
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.2, p.14 (PDF p.15)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory
open scoped RealInnerProductSpace

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.2, p.14 (PDF p.15).

There is an absolute linear bit lower bound for exact one-pass computation of `M₁`, already on
streams of at most `d+1` standard basis vectors. -/
theorem theorem_4_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ∀ (S Omega : Type) [Fintype S] [Nonempty S] [MeasurableSpace Omega]
        (mu : Measure Omega) [IsProbabilityMeasure mu]
        (A : CosDensity.StreamAlg (EuclideanSpace ℝ (Fin d)) Omega S),
        (∀ P : List (EuclideanSpace ℝ (Fin d)),
          P.length ≤ d + 1 →
          (∀ x ∈ P, ∃ j : Fin d, x j = 1 ∧ ∀ k : Fin d, k ≠ j → x k = 0) →
          CosDensity.SucceedsWP mu
            (fun omega => A.estimate omega P = CosDensity.moment 1 P) (2 / 3 : ENNReal)) →
        c * d ≤ CosDensity.memoryBits S := by sorry

end CosDensity.Supplement
