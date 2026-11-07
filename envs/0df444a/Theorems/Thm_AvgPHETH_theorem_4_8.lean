-- Prove2me | Theorems.Thm_AvgPHETH_theorem_4_8
-- name    : AvgPHETH.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:30.173759+00:00
-- url     : https://prove2.me/theorems/ffae5ee7-5d26-4232-88a4-70dc91ad357a
-- title:
--   Theorem 4.8 — Chain Rule: $\sum_i K^{t^c,O}(z_i\mid z_{<i})\le K^{t,O}(z_1,\dots,z_q)+cq\log t$
-- statement:
--   Let $U$ be an efficient universal machine, let $O$ be any oracle and assume $\Delta_2^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$. There is a constant $c\ge1$ such that for any $q\in\mathbb N$ and $z_1,\dots,z_q\in\{0,1\}^*$ with $N=\sum_i|z_i|\ge2$, and any $t\ge N^c$,
--
--   $$\sum_{i=1}^q K^{t^c,O}(z_i\mid z_1,\dots,z_{i-1})\le K^{t,O}(z_1,\dots,z_q)+cq\log t.$$
--
--   This is the time-bounded analogue of the chain rule, imported in the paper from [HN26; KK26], with a logarithmic cost per component.
--
--   Differences from the source:
--   - generalization: an efficient universal machine $U$, fixed once → every $U$ with polynomial overhead (IsEfficientUniversal); reason: the page prints no overhead bound; the usual efficient machines have polynomial overhead, so this specializes to any of them
--   - encoding: $\log$, values possibly undefined → base-2 logarithm, sum in $\mathbb R_{\ge0}\cup\{\infty\}$ with $K^t=\infty$ when no program exists; reason: Lean convention; a finite value is unchanged
--   - encoding: a fixed encoding of the tuple → binTuple; reason: a tuple encoding changes the complexity only by an additive constant and a polynomial in time
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.8, p.18 (PDF 20)

import Mathlib
import Definitions.Def_AvgPHETH_IsEfficientUniversal
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_Delta2PO
import Definitions.Def_AvgPHETH_Kt
import Definitions.Def_AvgPHETH_binTuple
open KarpLiptonOM
open scoped ENNReal

namespace AvgPHETH

/-- **Theorem 4.8 (Chain Rule [HN26; KK26])** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.18 (PDF 20)). Let `O` be any oracle and assume
`Δ₂^{p,O} × {U, T} ⊆ AvgP^O`. There is a constant `c ≥ 1` such that, for any `q` and `z₁, …, z_q`, with
`N = ∑ |z_i| ≥ 2` and `t ≥ N^c`, `∑_i K^{t^c,O}(z_i | z₁, …, z_{i−1}) ≤ K^{t,O}(z₁, …, z_q) + c q log t`.

**Formalization Note** Tuples are encoded by `binTuple`; for `i` the first index, the condition is the empty tuple,
which is the empty string. The sum is in `ℝ≥0∞`. -/
theorem theorem_4_8 (U : OracleTM) (hU : IsEfficientUniversal U) (O : Set (List Bool))
    (hAvg : TimesUT O (Delta2PO O)) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (q : ℕ) (zs : Fin q → List Bool) (t : ℕ),
      2 ≤ ∑ i, (zs i).length → (∑ i, (zs i).length) ^ c ≤ t →
      ∑ i : Fin q, ((Kt U O (t ^ c) (zs i) (binTuple ((List.ofFn zs).take (i : ℕ))) : ℕ∞) : ℝ≥0∞) ≤
        ((Kt U O t (binTuple (List.ofFn zs)) [] : ℕ∞) : ℝ≥0∞) +
          ENNReal.ofReal ((c : ℝ) * (q : ℝ) * Real.logb 2 t) := by sorry

end AvgPHETH
