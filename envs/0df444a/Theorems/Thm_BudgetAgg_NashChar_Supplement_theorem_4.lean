-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_4
-- name    : BudgetAgg.NashChar.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:09:03.898692+00:00
-- url     : https://prove2.me/theorems/a064d0a5-4ed9-487f-9e92-dca544da3e46
-- title:
--   Theorem 4 — with Leximin-Leontief preferences, NASH is the only continuous strategyproof mechanism with core fair share
-- statement:
--   Assume Leximin-Leontief preferences, while NASH still maximizes the product of the Leontief utilities $u_i(q)=\min_{j:p_{i,j}>0}q_j/p_{i,j}$. A mechanism $f$ is continuous, strategyproof and satisfies core fair share (both for the leximin relations) if and only if $f=\mathrm{NASH}$:
--
--   $$\big(f\text{ continuous}\ \wedge\ f\text{ lex-strategyproof}\ \wedge\ \forall P\ f(P)\text{ lex-core fair share}\big)\iff\forall P:\ f(P)=\mathrm{NASH}(P).$$
--
--   This is a companion theorem: the goal (Theorem 3) is not proved from it. Compared with Theorem 3, group-strategyproofness is weakened to strategyproofness. Its "if" direction rests on Proposition 1, Theorem 7 and Proposition 6; its "only if" direction on Lemma 16 and the leximin versions of Lemmas 10 and 11.
--
--   **Formalization Note** $n,m\ge1$.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: NASH(P) = argmax_{q∈∆m} ∏_i u_i(q), a distribution → IsNashOutcome P q: q is a distribution maximizing the Nash product; "f = NASH" is ∀ P, IsNashOutcome P (f P); reason: the maximizer is unique (published BudgetAgg.NashChar.nash_unique), so the predicate pins down NASH(P)
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the subtype/product topology; reason: all norms on a finite-dimensional space induce the same topology, as p. 8 notes
--   - reading: core fair share: no blocking coalition N′ ⊆ N (Definition 3) → only nonempty coalitions S are excluded from blocking; reason: for N′ = ∅ the condition "for all i ∈ N′" holds vacuously, so ∅ would block every distribution and no mechanism could satisfy the axiom; the base mission reads Definition 3 the same way
--   - reading: "NASH is the only continuous mechanism that satisfies …" → an iff: the three properties hold for f exactly when f selects the Nash outcome at every profile; reason: "the only" asserts both that NASH has the properties and that no other mechanism has them; the base Theorem 3 is posed the same way
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 17, Theorem 4 (proof App. G, pp. 39–44)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 4, p. 17: with Leximin-Leontief preferences, NASH is the only continuous
mechanism that satisfies strategyproofness and core fair share. -/
theorem theorem_4 {n m : ℕ} [NeZero n] [NeZero m] (f : Mechanism n m) :
    (Continuous f ∧ IsLexStrategyproof f ∧ ∀ P, IsLexCoreFairShare P (f P)) ↔
      (∀ P, IsNashOutcome P (f P).1) := by sorry

end BudgetAgg.NashChar.Supplement
