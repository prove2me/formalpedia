-- Prove2me | Theorems.Thm_BehrendWindows_exists_large_noRelation
-- name    : BehrendWindows.exists_large_noRelation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:50:33.239752+00:00
-- url     : https://prove2.me/theorems/e47587a2-596d-43de-bdaa-58d6c1dfad4f
-- title:
--   The release's normalisation: large sets with no $L$-relation
-- statement:
--   There is a constant $C>0$ such that for all natural numbers $L\ge 2$ and $n$ there is a finite set $T$ of integers with
--
--   1. $0\le s$ and $4Ls<n$ for every $s\in T$,
--   2. no $L$-relation in $T$ (no pairwise distinct $s_1,s_2,s_3\in T$ and distinct non-zero integers $i,j$ with $|i|,|j|\le L$ satisfy $j(s_2-s_1)=i(s_3-s_1)$),
--   3. the size bound
--   $$|T|\ \ge\ \frac{n}{L}\exp\!\Big(-C\sqrt{\log n\,\log L}\Big).$$
--
--   This is the normalisation in which the property is used in the Lean development accompanying L. Alpöge's November 2026 announcement, and it follows from the goal theorem with $m=2L+1$.
--
--   **Formalization Note** The condition $0\le s$ is required: without it, negative elements would make the range condition $4Ls<n$ empty.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 9; L. Alpöge, Remark (20 Nov 2026), https://alpo.ge/remark.pdf

import Mathlib
import Definitions.Def_BehrendWindows_NoRelation

namespace BehrendWindows

theorem exists_large_noRelation :
    ∃ C : ℝ, 0 < C ∧ ∀ L n : ℕ, 2 ≤ L → ∃ T : Finset ℤ,
      (∀ s ∈ T, 0 ≤ s ∧ 4 * L * s < n) ∧ NoRelation T L ∧
      ((n : ℝ) / L) * Real.exp (-C * Real.sqrt (Real.log n * Real.log L)) ≤ (T.card : ℝ) := by sorry

end BehrendWindows
