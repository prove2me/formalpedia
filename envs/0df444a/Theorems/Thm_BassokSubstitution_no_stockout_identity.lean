-- Prove2me | Theorems.Thm_BassokSubstitution_no_stockout_identity
-- name    : BassokSubstitution.no_stockout_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:39:48.682806+00:00
-- url     : https://prove2.me/theorems/baf761ca-3ef8-48bc-b15f-c184791601f7
-- title:
--   Lemma 1 — decomposition of the no-stock-out probability of class $i$
-- statement:
--   Consider the model with Assumptions 1–3, $b \ge 0$, independent nonnegative demands with densities and finite means, and stock levels $y \ge 0$. For classes $k < i$,
--   $$\Pr\{S^i_i = 0\} + \sum_{m=k}^{i-1} \Pr\{S^{m+1}_i > 0,\ \vec S^m_{m,i} = 0\} = 1 - \Pr\{S^k_i > 0\},$$
--   where $S^m_j$ is the shortage of class $j$ in the subproblem with products $m, \dots, j$ and $\vec S^m_{m,i} = 0$ means that none of the classes $m, \dots, i$ is short in its subproblem starting at product $m$.
--
--   The identity splits the event "class $i$ is not short when products $k, \dots, i$ are available" according to the least flexible product that already suffices. It is used, with Lemmas 2 and 5, to bound the salvage terms in the proof of Theorem 2.
--
--   **Formalization Note.** The paper prints the sum with "…"; its general term is $\Pr\{S^{m+1}_i > 0, \vec S^m_{m,i} = 0\}$ for $m = i-1$ down to $k$. Indices are 0-based in Lean. The model hypotheses are those of the whole mission; the identity itself does not need independence.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, Lemma 1

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 1: for classes `k < i` (0-based), the probability of no shortage of class `i` in the
subproblem with products `k, …, i` decomposes according to the first product (from `i`
downwards) whose subproblem already has no shortage of class `i`. -/
theorem no_stockout_identity {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    (Measure.pi ν).real {d | shortage y d i i = 0}
        + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
            (Measure.pi ν).real {d | 0 < shortage y d (m + 1) i ∧ ShortVecZero y d m m i}
      = 1 - (Measure.pi ν).real {d | 0 < shortage y d k i} := by sorry

end BassokSubstitution
