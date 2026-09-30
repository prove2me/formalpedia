-- Prove2me | Theorems.Thm_Computability_friedberg_muchnik
-- name    : Computability.friedberg_muchnik
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T19:38:35.152607+00:00
-- url     : https://prove2.me/theorems/f8667d51-9f79-4281-aa2c-9b64f99087eb
-- title:
--   Friedberg–Muchnik theorem: two Turing incomparable c.e. sets
-- statement:
--   There exist two computably enumerable sets $A,B\subseteq\mathbb N$ such that neither set is Turing reducible to the other:
--
--   $$\exists A,B\subseteq\mathbb N,\qquad A\text{ is c.e.}\;\land\;B\text{ is c.e.}\;\land\;A\not\le_T B\;\land\;B\not\le_T A.$$
--
--   Here computable enumerability means that membership is semidecidable. The relation $A\le_T B$ means that a computation with access to the total membership oracle for $B$ decides membership in $A$ on every input. Thus both possible directions of oracle computation are excluded. This is the two-set Friedberg–Muchnik theorem, matching Miller's Theorem 26.2 on page 51.
--
--   **Formalization Note** The target has no hypotheses and retains the supplied statement in namespace `Computability`. It uses Mathlib's `REPred` and Turing reducibility through the imported set definitions. The degree-quotient helpers are included in the definition bundle but are not needed to state this goal.
-- source:
--   Richard M. Friedberg (1957), Two recursively enumerable sets of incomparable degrees of unsolvability (solution of Post's problem, 1944), PNAS 43(2), 236–238. DOI: https://doi.org/10.1073/pnas.43.2.236; free archive: https://pmc.ncbi.nlm.nih.gov/articles/PMC528418/. Exact two-set statement and working proof reference: Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, statement p. 51, proof pp. 51–54: https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51. Earlier independent contribution: A. A. Muchnik (1956), On the unsolvability of the problem of reducibility in the theory of algorithms, Doklady Akademii Nauk SSSR 108(2), 194–197 (Russian); Math-Net bibliography: https://www.mathnet.ru/rus/person46479.

import Definitions.Def_friedberg_muchnik_sets

namespace Computability

/-- There are two computably enumerable sets of incomparable Turing degree. -/
theorem friedberg_muchnik :
    ∃ A B : Set ℕ,
      CEnumerable A ∧
      CEnumerable B ∧
      TuringIncomparable A B := by sorry

end Computability
