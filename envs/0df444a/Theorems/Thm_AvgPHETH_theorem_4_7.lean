-- Prove2me | Theorems.Thm_AvgPHETH_theorem_4_7
-- name    : AvgPHETH.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:33:56.91584+00:00
-- url     : https://prove2.me/theorems/a6b54ec6-418a-458d-8ea4-2ee08fa535dd
-- title:
--   Theorem 4.7 — Oracle Elimination: $K^{t^c,O}(z)\le K^{t,O\oplus A}(z)+c\log t$
-- statement:
--   Let $U$ be an efficient universal machine. Suppose $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$ for an oracle $O$ and a fixed $d\ge1$. For every $A\in\Sigma_d^{p,O}$ there is a constant $c\ge1$ such that for all strings $z$ and all $t\ge\max\{2,|z|\}$,
--
--   $$K^{t^c,O}(z)\le K^{t,O\oplus A}(z)+c\log t.$$
--
--   Under average-case easiness, a short description that uses the oracle $A$ yields a description of nearly the same length that does not, at the price of a polynomial increase in time. The paper imports this from [Hir20b]; it is the step that removes oracles from the compressed moves.
--
--   Differences from the source:
--   - generalization: an efficient universal machine $U$, fixed once → every $U$ with polynomial overhead (IsEfficientUniversal); reason: the page prints no overhead bound; the usual efficient machines have polynomial overhead, so this specializes to any of them
--   - encoding: $\log$, values possibly undefined → base-2 logarithm, sum in $\mathbb R_{\ge0}\cup\{\infty\}$ with $K^t=\infty$ when no program exists; reason: Lean convention; a finite value is unchanged
--   - encoding: $\Sigma_d^{p,O}$ on the usual machine → the two-tape machine KarpLiptonOM.OracleTM; reason: same classes up to polynomial overhead
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 4.7, p.18 (PDF 20)

import Mathlib
import Definitions.Def_AvgPHETH_IsEfficientUniversal
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_Kt
import Definitions.Def_AvgPHETH_oJoin
open KarpLiptonOM
open scoped ENNReal

namespace AvgPHETH

/-- **Theorem 4.7 (Oracle Elimination Lemma [Hir20b])** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.18 (PDF 20)). If
`Σ_{d+1}^{p,O} × {U, T} ⊆ AvgP^O` for an oracle `O` and a fixed `d ≥ 1`, then for every `A ∈ Σ_d^{p,O}` there is a
constant `c ≥ 1` such that, for all `z` and `t ≥ max{2, |z|}`, `K^{t^c,O}(z) ≤ K^{t,O⊕A}(z) + c log t`.

**Formalization Note** The sum is in `ℝ≥0∞`, since `K^t` may be `⊤`. The constant `c` comes after `U`, `O`, `d`, `A`
and before `z`, `t`. `log` is base 2. -/
theorem theorem_4_7 (U : OracleTM) (hU : IsEfficientUniversal U) (O : Set (List Bool)) (d : ℕ)
    (hd : 1 ≤ d) (hAvg : TimesUT O (SigmaPO O (d + 1))) (A : Set (List Bool))
    (hA : A ∈ SigmaPO O d) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (z : List Bool) (t : ℕ), max 2 z.length ≤ t →
      ((Kt U O (t ^ c) z [] : ℕ∞) : ℝ≥0∞) ≤
        ((Kt U (oJoin O A) t z [] : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal ((c : ℝ) * Real.logb 2 t) := by sorry

end AvgPHETH
