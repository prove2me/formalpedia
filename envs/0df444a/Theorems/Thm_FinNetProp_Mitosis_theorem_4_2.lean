-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_theorem_4_2
-- name    : FinNetProp.Mitosis.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:34.077055+00:00
-- url     : https://prove2.me/theorems/4f6e12a3-d0ce-4f19-aa2f-a6a6627c329b
-- title:
--   Theorem 4.2, p. 2805 — the proportional rule is the unique bankruptcy rule satisfying claims boundedness, limited liability, priority of creditors, continuity, impartiality and invariance to mitosis
-- statement:
--   **Theorem 4.2.** The proportional rule $p$ is the unique bankruptcy rule satisfying the axioms of claims boundedness, limited liability, priority of creditors, continuity, impartiality, and invariance to mitosis.
--
--   Precisely, the statement has two parts.
--
--   1. For every financial network $F = (N, z, L)$ there is exactly one payment matrix $P \in \mathcal M(N)$ solving
--   $$P_{ij} = \min\Big\{\Pi_{ij}\Big(z_i + \sum_{k \in N} P_{ki}\Big),\ L_{ij}\Big\}, \qquad i, j \in N, \tag{2.1}$$
--   so the proportional rule $p$, which assigns this solution to $F$, is a well-defined bankruptcy rule.
--
--   2. A bankruptcy rule $b$ satisfies claims boundedness (Axiom 3.1), limited liability (Axiom 3.2), priority of creditors (Axiom 3.3), continuity (Axiom 3.4), impartiality (Axiom 3.5) and invariance to mitosis (Axiom 4.1) if and only if, for every financial network $F$, $b(F)$ solves (2.1) for $F$, that is, $b = p$.
--
--   The result characterizes the proportional rule of Eisenberg and Noe (2001), the clearing rule used in most stress-testing models of interbank networks, by properties of bankruptcy rules alone, without assuming a priori that payments depend only on asset values and liabilities.
--
--   **Formalization Note** "$b = p$" is expressed as "$b(F)$ solves (2.1) for every $F$"; together with part 1 this is equality with the proportional rule. Part 1 is included so that the statement asserts that $p$ exists; without it the characterization could hold for an empty class.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2805, Theorem 4.2 (with Definition 2.2, p. 2801)

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem theorem_4_2 :
    (∀ F : FinNet, ∃! P : ℕ → ℕ → ℝ, IsPropSolution F P) ∧
      ∀ b : BankruptcyRule,
        (ClaimsBounded b ∧ LimitedLiability b ∧ PriorityOfCreditors b ∧ RuleContinuous b ∧
            Impartial b ∧ InvariantToMitosis b) ↔
          ∀ F : FinNet, IsPropSolution F (b F) := by sorry

end FinNetProp.Mitosis
