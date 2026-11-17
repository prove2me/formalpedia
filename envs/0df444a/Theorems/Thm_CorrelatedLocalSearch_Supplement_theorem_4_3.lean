-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_4_3
-- name    : CorrelatedLocalSearch.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:07:21.46877+00:00
-- url     : https://prove2.me/theorems/701c6d5f-11fe-4c29-99fc-135bc2841a91
-- title:
--   Theorem 4.3 — matching delay across the source threshold
-- statement:
--   There are positive constants $c_{k,r},C_{k,r}$ such that for every $s\in[s_*,1]$, $h\ge r$ and $D\ge1$, some complete formula has a nonsatisfying initial assignment at distance $h$ from its unique all-one strong witness and one source $\nu\in\mathcal Q_{s,D}$ satisfying, simultaneously for every selector,
--   $$\tau\ge c_{k,r}\Psi_s(h+\log D+1)\quad\nu\text{-almost surely},$$
--   with $n\le C_{k,r}\Psi_s(h+\log D+1)$.
--
--   Differences from the source:
--   - encoding: $O_{k,r}$ → one positive constant quantified before all instances; reason: expands the uniform asymptotic bound
--   - encoding: $L/0=\infty$ → the second branch of $\Psi_s$ is $\top$ in ENNReal at $s=s_*$; reason: exact extended-value convention
--   - encoding: the almost-sure delay compares a possibly infinite stopping time with a nonnegative bound → `\mathbb N\cup\{\infty\}` and `ENNReal`; reason: exact extended-nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_SAT

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.3, p.11 (PDF p.13).
A single admissible source forces the full cubic-to-linear delay almost surely, simultaneously for
every selector, on a complete formula whose size has matching order. -/
theorem theorem_4_3 (k r : Nat) (hk : k < 2 * r) (hr : r < k) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ s, CorrelatedLocalSearch.sStar k r ≤ s -> s ≤ 1 ->
        ∀ h : Nat, r ≤ h -> ∀ D : Real, 1 ≤ D ->
          ∃ (n : Nat) (x0 : Fin n -> Bool) (nu : Measure (Nat -> Fin k)),
            ¬ CorrelatedLocalSearch.Satisfies (completeFormula k r n) x0 ∧
            hammingDist x0 (allOneAssignment n) = h ∧
            CorrelatedLocalSearch.IsStrongWitness r (completeFormula k r n) (allOneAssignment n) ∧
            (∀ xs, CorrelatedLocalSearch.IsStrongWitness r (completeFormula k r n) xs ->
              xs = allOneAssignment n) ∧
            nu ∈ CorrelatedLocalSearch.SourceClass k s D ∧
            (∀ sel, CorrelatedLocalSearch.IsValidSelector (completeFormula k r n) sel ->
              nu {omega | ENNReal.ofReal c *
                  Psi k r s ((h : Real) + Real.log D + 1) ≤
                ((CorrelatedLocalSearch.walkTau (completeFormula k r n) sel x0 omega : ℕ∞) : ENNReal)} = 1) ∧
            (n : Real) ≤ C * (Psi k r s ((h : Real) + Real.log D + 1)).toReal := by sorry

end CorrelatedLocalSearch.Supplement
