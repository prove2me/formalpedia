-- Prove2me | Theorems.Thm_AgnHalfMem_Supplement_theorem_5_2
-- name    : AgnHalfMem.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:58:47.386201+00:00
-- url     : https://prove2.me/theorems/9cfb380d-8513-45db-ac8c-1f7acd97ece7
-- title:
--   Theorem 5.2 — under a known marginal, realizable halfspaces are learnable with $O(d\log^2(d/\varepsilon))$ bits and $\mathrm{poly}(d,1/\varepsilon)$ samples
-- statement:
--   There are constants $C,B>0$ such that the following holds for every dimension $d$, every probability distribution $\mu$ on $\mathbb R^d$ and every $\varepsilon\in(0,1/4)$. There is a private-coin streaming algorithm, which may depend on $d$, $\mu$ and $\varepsilon$, with at most
--   $$
--   2^{\,C\,d\,\log_2^2(d/\varepsilon)}\ \text{memory states}\qquad\text{and at most}\qquad C\Big(\frac d\varepsilon\Big)^{B}\ \text{samples},
--   $$
--   such that for every unit vector $w^*\in\mathbb R^d$, run on i.i.d. samples $(x,\mathrm{sign}(\langle w^*,x\rangle))$ with $x\sim\mu$, it outputs with probability at least $2/3$ a Boolean hypothesis $h:\mathbb R^d\to\{-1,1\}$ with misclassification error
--   $$
--   \Pr_{x\sim\mu}\big[h(x)\ne\mathrm{sign}(\langle w^*,x\rangle)\big]\ \le\ \varepsilon .
--   $$
--
--   In words, $O(d\log^2(d/\varepsilon))$ bits of memory and $\mathrm{poly}(d,1/\varepsilon)$ samples suffice to learn halfspaces in the realizable setting under any known marginal, which contrasts with the agnostic lower bound of Theorem 4.10.
--
--   **Formalization Note** The algorithm is a deterministic measurable branching program that reads a fresh private coin $u\sim\mathrm{Unif}[0,1]$ with each sample. Memory of $b$ bits means at most $2^b$ states. The output may be any classifier.
--
--   Differences from the source:
--   - encoding: O(d log²(d/ε)) bits, poly(d, 1/ε) samples → card S ≤ 2^{C·d·(log₂(d/ε))²}, (T:ℝ) ≤ C·(d/ε)^B with universal C, B chosen before d, µ, ε; reason: b bits is at most 2^b states; every polynomial in d ≥ 1 and 1/ε > 4 is bounded by C(d/ε)^B, and C(d/ε)^B is a polynomial
--   - encoding: "distribution-dependent PAC learning algorithm", "a distribution realizable by a halfspace with a fixed marginal µ" → the algorithm is chosen after d, µ, ε and before the unit w*; the samples are realizLaw µ w* (x ∼ µ, label sign⟨w*,x⟩); µ any probability measure on Fin d → ℝ; reason: p.19 "µ is the known marginal distribution", the target w* is unknown
--   - encoding: the algorithm's randomness ("internal random bits", p.21) → a deterministic measurable branching program fed ((x,u),y) with a fresh coin u ∼ Unif[0,1] per sample, output = leaf label read at coin 0; reason: private randomness counted in memory; a public seed would be free memory
--   - encoding: d ≥ 1 implicit → every d : ℕ; reason: at d = 0 there is no unit vector w*, so the case is vacuous
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 5.2, p.19 (proof pp.19–21)

import Mathlib
import Definitions.Def_AgnHalfMem_err
import Definitions.Def_AgnHalfMem_BP
import Definitions.Def_AgnHalfMem_Supplement_coinStream
import Definitions.Def_AgnHalfMem_Supplement_realizLaw

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Theorem 5.2 (distribution-dependent realizable upper bound).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Theorem 5.2, p.19: "There exists a distribution-dependent PAC
learning algorithm such that, for any ε ∈ (0, 1/4), given a stream of samples drawn from a
distribution realizable by a halfspace with a fixed marginal µ, the algorithm uses
O(d log²(d/ε)) bits of memory and poly(d, 1/ε) samples, and with probability at least 2/3 outputs
a Boolean hypothesis with misclassification error at most ε." Proof: pp.19–21.

There are constants `C, B > 0` such that for every `d`, every probability measure `µ` on `ℝ^d`
and every `ε ∈ (0, 1/4)` there is a measurable private-coin streaming algorithm (depending on
`d, µ, ε`) with at most `2^{C d (log₂(d/ε))²}` memory states and at most `C (d/ε)^B` samples
which, for every unit vector `w*`, on samples `(x, sign⟨w*, x⟩)` with `x ∼ µ` outputs with
probability at least `2/3` a Boolean hypothesis with misclassification error at most `ε`.

**Formalization Note.** `O(·)` is the explicit constant `C` and `poly(d, 1/ε)` is `C (d/ε)^B`
(every polynomial in `d ≥ 1` and `1/ε ≥ 1` is bounded by such a monomial). The algorithm may
depend on `µ` ("distribution-dependent"; p.19 "µ is the known marginal") but not on `w*`. Its
randomness is one fresh private coin per sample (`coinStream`, `pcOutput`); memory of `b` bits is
`Fintype.card S ≤ 2^b`. The output may be any Boolean hypothesis. -/
theorem theorem_5_2 :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (d : ℕ) (μ : Measure (Fin d → ℝ)), IsProbabilityMeasure μ →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ (S : Type) (_ : Fintype S) (T : ℕ) (b : BP S ((Fin d → ℝ) × ℝ) T),
        b.IsMeasurableBP ∧
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (C * d * Real.logb 2 (d / ε) ^ 2) ∧
        (T : ℝ) ≤ C * ((d : ℝ) / ε) ^ B ∧
        ∀ w : Fin d → ℝ, ∑ i, w i ^ 2 = 1 →
          ENNReal.ofReal (2 / 3) ≤
            (Measure.pi fun _ : Fin T => coinStream (realizLaw μ w))
              {s | err (realizLaw μ w) (pcOutput b s) ≤ ε} := by sorry

end Supplement

end AgnHalfMem
