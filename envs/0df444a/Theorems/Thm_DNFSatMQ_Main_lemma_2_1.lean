-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_2_1
-- name    : DNFSatMQ.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:24.670016+00:00
-- url     : https://prove2.me/theorems/cfc72005-6f2a-401e-8b7d-5d0a365f3fcc
-- title:
--   Lemma 2.1 — total variation between uniform laws on finite sets
-- statement:
--   For nonempty finite sets $A, B$ (subsets of one finite set), let $U_A, U_B$ be the uniform laws and $d_{TV}(D,D') = \frac12\sum_x |D(x)-D'(x)|$. Then
--   $$d_{TV}(U_A, U_B) = 1 - \frac{|A\cap B|}{\max\{|A|,|B|\}} \le \frac{|A \triangle B|}{|A|},$$
--   with $A\triangle B = (A\setminus B)\cup(B\setminus A)$. The lemma converts a classification error $|F\triangle H|$ into the distance $d_{TV}(U_H, U_F)$ required by Problem 1.1.
--
--   Differences from the source:
--   - encoding: A, B nonempty finite sets → `Finset`s of one finite type α; d_TV is the published `SSNonExt.TV` of `PMF.uniformOfFinset`; reason: both laws must live on one space for d_TV; any two finite sets lie in a common finite set
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 2.1, p. 5 (PDF 6)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-- Lemma 2.1 (p. 5). -/
theorem lemma_2_1 {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    SSNonExt.TV (PMF.uniformOfFinset A hA) (PMF.uniformOfFinset B hB) =
        1 - ((A ∩ B).card : ℝ) / (max A.card B.card : ℕ) ∧
      1 - ((A ∩ B).card : ℝ) / (max A.card B.card : ℕ) ≤ (((A \ B) ∪ (B \ A)).card : ℝ) / A.card := by sorry

end DNFSatMQ.Main
