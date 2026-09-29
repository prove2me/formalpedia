-- Prove2me | Theorems.Thm_Erdos9796Mission_combined
-- name    : Erdos9796Mission.combined
-- status  : Disproved
-- author  : @mysticflounder
-- created : 2026-09-05T22:52:54.751647+00:00
-- url     : https://prove2.me/theorems/a6bf5110-b91e-4a2c-9d03-8b51a8a9e6ad
-- title:
--   Erdős Problems 97 and 96: the combined convex-distance mission
-- statement:
--   Establish both affirmative statements in one package: every nonempty finite convex-independent planar point set has a vertex with no four other vertices at a common positive distance, and the maximum number of unordered unit-distance pairs among convex-independent $n$-point sets is $O(n)$.
--
--   $$\text{Problem 97}\;\land\;\text{Problem 96}.$$
--
--   The two targets are linked by deletion: Problem 97 supplies a vertex of unit degree at most three in every nonempty remaining subset, so counting each edge when its first endpoint is removed gives at most $3n$ unordered unit-distance pairs. No implication from Problem 96 back to Problem 97 is asserted. Both statements are open targets, not assumptions hidden in the definitions.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/README.md; https://www.erdosproblems.com/97; https://www.erdosproblems.com/96

import Definitions.Def_Erdos9796Mission

/-!
The combined open Erdős Problems 97 and 96 mission statement.
-/

theorem Erdos9796Mission.combined :
    Erdos9796Mission.Problem97 ∧ Erdos9796Mission.Problem96 := by sorry
