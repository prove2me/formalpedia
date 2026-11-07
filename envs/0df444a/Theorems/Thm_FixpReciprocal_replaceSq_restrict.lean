-- Prove2me | Theorems.Thm_FixpReciprocal_replaceSq_restrict
-- name    : FixpReciprocal.replaceSq_restrict
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:53:25.86049+00:00
-- url     : https://prove2.me/theorems/70367de1-eca1-40c5-812c-5fb13df51c79
-- title:
--   Theorem 4.2 (proof, hardness) — solutions of $\mathcal C'$ restrict to solutions of $\mathcal C$
-- statement:
--   Let $\tau>0$ be rational and $\mathcal C$ a circuit of $N$ gates over the functions of Lemma 3.4, with replacement circuit $\mathcal C'$. Then:
--
--   1. $\mathcal C'$ is a valid circuit, with $N\le|\mathcal C'|\le7N$ gates;
--   2. every solution of $\mathcal C'$ restricts on the first $N$ coordinates to a solution of $\mathcal C$;
--   3. every solution of $\mathcal C$ extends in exactly one way to a solution of $\mathcal C'$.
--
--   The conclusion holds with cycles and for gates $x_i=x_i^2$, because fresh variables of different replaced gates are disjoint.
--
--   Differences from the source:
--
--   - reading: the six fresh values are uniquely determined by acyclic evaluation, and the remaining equation holds exactly when x_i = x_j² → a solution of C extends in exactly one way to a solution of C′; reason: this is the two sentences' content for solutions, in one clause; the paper's stated conclusion is the restriction clause
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_RGate
import Definitions.Def_FixpReciprocal_squareProblem
import Definitions.Def_FixpReciprocal_replaceSq

namespace FixpReciprocal

/-- **Proof of Theorem 4.2, restriction.** "For every fixed assignment `x ∈ [0, 1]^N` to the original variables,
the six fresh intermediate values replacing a gate `x_i = x_j²` are uniquely determined by acyclic evaluation on
input `x_j`. By Lemma 4.1, the remaining equation, whose output is the retained variable `x_i`, holds exactly when
`x_i = x_j²`. Thus every solution of `C′` restricts to a solution of `C`. The fresh intermediate variables for
different replaced gates are disjoint, so this conclusion also holds for cycles and for `i = j`. The new circuit
has at most `7N` gates".

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12.

**Formalization Note.** The last clause packages "uniquely determined" and "holds exactly when": a solution
of `C` extends in exactly one way to a solution of `C′`. -/
theorem replaceSq_restrict (τ : ℚ) (hτ : 0 < τ) (C : List SqGate) (hC : SqValid C) :
    RValid (replaceSq τ C) ∧
    C.length ≤ (replaceSq τ C).length ∧
    (replaceSq τ C).length ≤ 7 * C.length ∧
    (∀ y ∈ RCircuitSol τ (replaceSq τ C), restrict C.length y ∈ SqCircuitSol C) ∧
    (∀ x ∈ SqCircuitSol C, ∃! y, y ∈ RCircuitSol τ (replaceSq τ C) ∧ restrict C.length y = x) := by sorry

end FixpReciprocal
