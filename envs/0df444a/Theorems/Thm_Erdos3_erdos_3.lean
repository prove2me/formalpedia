-- Prove2me | Theorems.Thm_Erdos3_erdos_3
-- name    : Erdos3.erdos_3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:08:28.485766+00:00
-- url     : https://prove2.me/theorems/a1db8c60-1097-413f-911f-0f9d4b2ec14f
-- title:
--   Erdős Problem 3: divergent reciprocal sums force long progressions
-- statement:
--   Let $A\subseteq\mathbb N$ satisfy $\displaystyle\sum_{n\in A}\frac1n=\infty$. Then $A$ contains arbitrarily long arithmetic progressions: for infinitely many $k$ (equivalently, for every $k$) there is a $k$-term progression $a,a+d,\dots,a+(k-1)d$ with $d>0$ all of whose terms lie in $A$.
--
--   This is the conjecture of Erdős (Erdős Problem #3), still open. The formal-conjectures entry states it as `answer(sorry) ↔ …`; here the answer is fixed to Erdős's conjectured answer **yes**, so a proof on the platform settles it affirmatively and a disproof (a proof of the negation) settles it negatively.
-- source:
--   Erdős Problem #3, https://www.erdosproblems.com/3; formal-conjectures FormalConjectures/ErdosProblems/3.lean (theorem erdos_3); the `answer(sorry)` placeholder is instantiated to `True` (the conjectured answer).

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem erdos_3 : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, IsAPOfLength S k := by
  sorry

end Erdos3
