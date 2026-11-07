-- Prove2me | Theorems.Thm_AlgoPFR_theorem_4_3_ggmt_decrement
-- name    : AlgoPFR.theorem_4_3_ggmt_decrement
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:31.970946+00:00
-- url     : https://prove2.me/theorems/5a8f678c-7140-49d8-a4ff-e0b2d8bade84
-- title:
--   Theorem 4.3 (GGMT decrement, [GGMT24]) — one of five families decreases $d$
-- statement:
--   There is a universal constant $\eta>0$ such that for all $n$ and all laws $X,Y$ on $\mathbb F_2^n$, at least one of the five raw candidate families (self-sum, cross-sum, self-fiber, cross-fiber, endgame), with $(X',Y')$ drawn according to its natural law, satisfies
--   $$\mathbb E\bigl[d[X';Y']+\eta\,d[X;X']+\eta\,d[Y;Y']\bigr]\le(1-\eta)\,d[X;Y].$$
--   For the two sum families the output laws are deterministic; for the other three the expectation is over the fiber or endgame labels.
--
--   This is the engine of the recursion. The source gives it as its own $\mathbb F_2^n$ formulation of a result of Gowers, Green, Manners and Tao.
--
--   Differences from the source:
--
--   - encoding: a universal constant η > 0 and the five families → ∃ η > 0 with IsDecrementConstant η: ∀ n X Y ∃ family; the expectation lies in [0, ∞]; reason: the same quantifiers; every term is nonnegative
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 4.3, p.19

import Mathlib
import Definitions.Def_AlgoPFR_Families

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Theorem 4.3 (GGMT decrement, [GGMT24]).** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.19: there is a universal constant `η > 0` such
that, for every pair `(X, Y)` of laws on `F₂ⁿ`, at least one of the five raw candidate families, with
`(X′, Y′)` drawn according to its natural law, satisfies
`E[d[X′;Y′] + η d[X;X′] + η d[Y;Y′]] ≤ (1 − η) d[X;Y]`. -/
theorem theorem_4_3_ggmt_decrement : ∃ η : ℝ, 0 < η ∧ IsDecrementConstant η := by sorry

end AlgoPFR
