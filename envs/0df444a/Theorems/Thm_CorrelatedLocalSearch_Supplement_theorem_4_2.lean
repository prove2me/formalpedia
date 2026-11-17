-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_4_2
-- name    : CorrelatedLocalSearch.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:06:02.514604+00:00
-- url     : https://prove2.me/theorems/6e915050-ec27-44a1-80ae-78ff84251e66
-- title:
--   Theorem 4.2 — sharp threshold and gap from every single depth
-- statement:
--   For the complete formula family, every $0<s<s_*$ admits one source forcing nontermination for every selector. Starting with exactly $r$ zeros, uniformly in $s\in[s_*,1]$, $N\ge3$ and $T\ge1$, the exact worst survival probability is bounded above and below by constant multiples in the exponent of
--   $$\exp\{-\Theta_{k,r}(T^{1/3}+(s-s_*)T+T/N^2)\}.$$
--   At $s=s_*$ and $1\le T\le N-2$, the infimum over all single-depth cover costs is bounded above and below by positive $k,r$-dependent constants times $(T+1)^{-3/2}$.
--
--   Differences from the source:
--   - encoding: $\Theta_{k,r}$ notation → positive upper and lower constants quantified before $n,s,T$; reason: expands uniform asymptotic notation without changing instances
--   - encoding: $N=n-k+2$ → natural-number expression under the source hypothesis $N\ge3$; reason: the hypothesis excludes truncation at the boundary
--   - encoding: worst probabilities and cover costs written as nonnegative real quantities → `ENNReal`; reason: exact extended-nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_SAT

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.2, p.11 (PDF p.13).
The complete formula family has the sharp threshold, the uniform three-regime two-sided survival
profile, and the two-sided polynomial cost for every single-depth cover. -/
theorem theorem_4_2 (k r : Nat) (hk : k < 2 * r) (hr : r < k) :
    ∃ cLower cUpper dLower dUpper : Real,
      0 < cLower ∧ 0 < cUpper ∧ 0 < dLower ∧ 0 < dUpper ∧
      (∀ s, 0 < s -> s < CorrelatedLocalSearch.sStar k r ->
        ∃ (n : Nat) (x0 : Fin n -> Bool) (nu : Measure (Nat -> Fin k)),
          nu ∈ CorrelatedLocalSearch.SourceClass k s 1 ∧
          ¬ CorrelatedLocalSearch.Satisfies (completeFormula k r n) x0 ∧
          ∀ sel, CorrelatedLocalSearch.IsValidSelector (completeFormula k r n) sel ->
            nu {omega | CorrelatedLocalSearch.walkTau (completeFormula k r n) sel x0 omega = ⊤} = 1) ∧
      ∀ n, 3 ≤ n - k + 2 -> ∀ (x0 : Fin n -> Bool), HasExactlyRZeros r x0 ->
        ∀ sel, CorrelatedLocalSearch.IsValidSelector (completeFormula k r n) sel ->
          (∀ s, CorrelatedLocalSearch.sStar k r ≤ s -> s ≤ 1 -> ∀ T : Nat, 1 ≤ T ->
            let X : Real := (T : Real) ^ ((1 : Real) / 3) +
              (s - CorrelatedLocalSearch.sStar k r) * T + T / ((n - k + 2 : Nat) : Real) ^ 2
            (∃ nu : Measure (Nat -> Fin k), nu ∈ CorrelatedLocalSearch.SourceClass k s 1 ∧
              nu (satSurvivalEvent (completeFormula k r n) sel x0 T) =
                completeWorstTail k r n s sel x0 T) ∧
              ENNReal.ofReal (Real.exp (-cUpper * X)) ≤ completeWorstTail k r n s sel x0 T ∧
              completeWorstTail k r n s sel x0 T ≤ ENNReal.ofReal (Real.exp (-cLower * X))) ∧
          ∀ T : Nat, 1 ≤ T -> T ≤ n - k ->
            ENNReal.ofReal (dLower * (T + 1 : Real) ^ (-(3 : Real) / 2)) ≤
              (⨅ t, completeSingleDepthCost k r n sel x0 T t) ∧
            (⨅ t, completeSingleDepthCost k r n sel x0 T t) ≤
              ENNReal.ofReal (dUpper * (T + 1 : Real) ^ (-(3 : Real) / 2)) := by sorry

end CorrelatedLocalSearch.Supplement
