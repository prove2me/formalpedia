-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_6_1
-- name    : CorrelatedLocalSearch.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:09:29.424698+00:00
-- url     : https://prove2.me/theorems/7484ff2f-9adf-428c-ad5d-5a72a848ea7b
-- title:
--   Theorem 6.1 — exact same-tape restart criterion
-- statement:
--   For a deterministic one-symbol algorithm from a fixed initial configuration, $\alpha_s=C_s(N)$ is strictly less than one if and only if some same-tape restart policy has a uniform geometric tail $DK\gamma^t$, and if and only if some policy terminates almost surely for every source in $\mathcal Q_{s,1}$. If $\alpha_s=1$, every restart policy has nontermination probability one under some policy-dependent source in $\mathcal Q_{s,1}$.
--
--   Differences from the source:
--   - encoding: reset and running-time prose → a prefix-indexed Boolean restart decision and the induced source-step stopping time; reason: the type enforces deterministic nonanticipation and at most one reset between steps
--   - encoding: the possibly infinite restart time and its event probabilities → an infinity-valued natural stopping time and `ENNReal` probabilities; reason: exact extended-nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 6.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_RestartSynthesis

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 6.1, p.15 (PDF p.17).
Strict nontermination capacity is equivalent to a same-tape exponential-tail restart and to robust
almost-sure termination; at equality every restart policy is defeated by a policy-dependent source. -/
theorem theorem_6_1 {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (hA : 2 ≤ Fintype.card A)
    (pi : A -> Real) (hpi : ∀ a, 0 < pi a) (hpisum : (∑ a, pi a) = 1)
    (s : Real) (hs0 : 0 < s) (hs1 : s ≤ 1) (M : OneSymbolAlgorithm A) :
    (restartCapacity pi s M < 1 ↔
      ∃ rho : SameTapeRestartPolicy A M,
        ∃ K gamma : Real, 0 ≤ K ∧ 0 < gamma ∧ gamma < 1 ∧
          ∀ D : Real, 1 ≤ D -> ∀ nu : Measure (Nat -> A), nu ∈ SourceClass pi s D ->
            ∀ t : Nat, nu {omega | (t : ℕ∞) < sameTapeRestartTau rho omega} ≤
              ENNReal.ofReal (D * K * gamma ^ t)) ∧
    (restartCapacity pi s M < 1 ↔
      ∃ rho : SameTapeRestartPolicy A M,
        ∀ nu : Measure (Nat -> A), nu ∈ SourceClass pi s 1 ->
          nu {omega | sameTapeRestartTau rho omega = ⊤} = 0) ∧
    (restartCapacity pi s M = 1 ->
      ∀ rho : SameTapeRestartPolicy A M,
        ∃ nu : Measure (Nat -> A), nu ∈ SourceClass pi s 1 ∧
          nu {omega | sameTapeRestartTau rho omega = ⊤} = 1) := by sorry

end CorrelatedLocalSearch.Supplement
