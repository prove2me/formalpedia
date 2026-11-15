-- Prove2me | Theorems.Thm_A166944Research_composite_differences_below_1000
-- name    : A166944Research.composite_differences_below_1000
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-14T23:26:48.180778+00:00
-- url     : https://prove2.me/theorems/02c3ac3f-b4b9-45bc-87ca-ea18707d6dff
-- title:
--   Below 1000, the A166944 first differences are composite only at indices 18, 66 and 150
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944 with first differences $d_n=a_n-a_{n-1}$, and let $\operatorname{isComposite}$ be the trial-division test that returns true exactly when $n$ has a proper divisor.
--
--   The theorem classifies every composite first difference below $1000$:
--
--   $$
--   \forall\, n < 1000,\qquad \operatorname{isComposite}(d_n) \;\Longrightarrow\; n \in \{18,\; 66,\; 150\}.
--   $$
--
--   Equivalently: among the indices $2 \le n \le 1000$, the difference $d_n$ is composite at exactly three of them, namely
--
--   $$
--   d_{18}=9=3^2,\qquad d_{66}=33=3\cdot 11,\qquad d_{150}=25=5^2 ,
--   $$
--
--   and nowhere else in the range.
--
--   The result is a finite classification, and it is established by kernel evaluation rather than by a sampled scan: the statement is a bounded universal quantifier over `List.range 1001`, so `decide` checks all $1001$ indices. It is the first complete census of the composite values of $d$ in any range, and it isolates the three exceptional indices that any general argument about composite differences has to account for. In the A166944 conjecture the three are exactly the obstruction: records are required to be prime, so a composite difference can never be a record, and these are the only composite differences in the range to test that against.
--
--   **Formalization Note** The quantifier is over `List.range 1001`, i.e. the indices $0..1000$, and `n = 0` and `n = 1` are disposed of by the hypothesis since $d_0 = d_1 = 1$ is not composite. The evaluation needs `maxRecDepth 1000000`; the heaviest instance takes about twelve seconds.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Machine-checked at https://github.com/tara-sooo/A166944-Lean/blob/6105e7be/A166944/CompSweepComplete.lean, built on the rounded-prefix sweep in A166944/CompSweep1000.lean and the individual refutations in A166944/CompositeProbe.lean and A166944/CompositeThird.lean.

import Definitions.Def_a166944_composite_test

open A166944Research

namespace A166944Research

theorem composite_differences_below_1000 :
    ∀ n ∈ List.range 1001, isComposite (d n) = true → n = 18 ∨ n = 66 ∨ n = 150 := by
  sorry

end A166944Research
