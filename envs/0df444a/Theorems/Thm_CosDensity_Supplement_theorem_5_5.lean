-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_5_5
-- name    : CosDensity.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:20:09.680349+00:00
-- url     : https://prove2.me/theorems/8d42f908-cb72-44e1-8197-3ba434a60cb0
-- title:
--   Theorem 5.5 — diversity-index approximation needs $\Omega(d^2)$ bits
-- statement:
--   Fix $0<\epsilon<1/5$. There exist constants $c>0$, $K$, and $d_0$ such that, for every $d\ge d_0$, any one-pass algorithm that returns a $(1+\epsilon)$-approximation to $M_{-1}$ with probability at least $2/3$ on every nonempty stream with strictly positive pairwise cosine, length at most $d^K$, and rational coordinates of height at most $d^K$, satisfies
--   $$\log_2|S|\ge c d^2.$$
--
--   Differences from the source:
--   - encoding: $\Omega(d^2)$, polynomial stream length, and $O(\log d)$-bit rational coordinates → constants $c>0,K,d_0$, length $\le d^K$, coordinate numerator and denominator $\le d^K$, and memory $\log_2|S|$; reason: this is the standard quantified reading of the theorem's asymptotic clauses
--   - encoding: success probability at least $2/3$ → inner probability at least $2/3$ for a persistent public seed; reason: this is the base mission's nonmeasurability-safe success convention
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 5.5, p.19 (PDF p.20)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg
import Definitions.Def_CosDensity_Supplement_diversityIndex

open MeasureTheory
open scoped RealInnerProductSpace

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 5.5, p.19 (PDF p.20).

For every fixed `epsilon` in `(0,1/5)`, correctness only on polynomial-length finite-precision
streams with strictly positive pairwise cosine already forces a quadratic number of bits. The
constants `c`, `K`, and `d₀` are chosen before the dimension and the algorithm. -/
theorem theorem_5_5 :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 5 →
      ∃ c : ℝ, 0 < c ∧ ∃ K d₀ : ℕ, ∀ d ≥ d₀,
        ∀ (S Omega : Type) [Fintype S] [Nonempty S] [MeasurableSpace Omega]
          (mu : Measure Omega) [IsProbabilityMeasure mu]
          (A : CosDensity.StreamAlg (EuclideanSpace ℝ (Fin d)) Omega S),
          (∀ P : List (EuclideanSpace ℝ (Fin d)),
            P ≠ [] → (∀ x ∈ P, x ≠ 0) →
            (∀ x ∈ P, ∀ y ∈ P, 0 < ⟪CosDensity.unitize x, CosDensity.unitize y⟫) →
            P.length ≤ d ^ K → CosDensity.IsBitBounded (d ^ K) P →
            CosDensity.SucceedsWP mu (fun omega =>
              CosDensity.IsApprox epsilon (diversityIndex P) (A.estimate omega P))
              (2 / 3 : ENNReal)) →
          c * (d : ℝ) ^ 2 ≤ CosDensity.memoryBits S := by sorry

end CosDensity.Supplement
