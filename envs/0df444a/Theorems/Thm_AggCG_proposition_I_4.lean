-- Prove2me | Theorems.Thm_AggCG_proposition_I_4
-- name    : AggCG.proposition_I_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:21.551205+00:00
-- url     : https://prove2.me/theorems/24ffbedf-b9b4-4847-9121-f6b7af9ed7cd
-- title:
--   Proposition I.4 — capacity of the restricted family
-- statement:
--   There is an absolute $C>0$ such that for every $m\ge 4$, the tree-size loss family on $X_m$ has a pseudo-dimension $d$ with
--   $$m\le d\le C\,m\log m.$$
--
--   Differences from the source:
--   - encoding: m ≤ Pdim ≤ O(m log m) → ∃ C > 0 before m, and for every m ≥ 4 a d with PseudoDim (pdimClass m) d, m ≤ d, d ≤ C m log m; reason: the published PseudoDim is a maximum; here it exists because the shattered sets are bounded, and C uniform in m is the meaning of O(·)
--   - reading: an unspecified "LP-based B&B" solver that counts all generated nodes → the relation BBSize over every LP optimum and every fractional variable, without pruning by bound; TreeSize is its least size; reason: the paper names no solver; on every gadget the optimum is unique and all runs have one size (lemma_I_1)
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), Proposition I.4, p.52 (PDF p.53)

import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_AggCG_pdimClass

namespace AggCG

/-- **Proposition I.4** (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), p.52, PDF p.53): for `m ≥ 4` the pseudo-dimension of the tree-size family on `X_m` exists and lies between `m` and `C m log m`, with one absolute `C` before `m`. -/
theorem proposition_I_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 4 ≤ m →
      ∃ d : ℕ, FoundationsML.Regression.PseudoDim (pdimClass m) d ∧ m ≤ d ∧
        (d : ℝ) ≤ C * m * Real.log m := by sorry

end AggCG
