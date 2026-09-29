-- Prove2me | Theorems.Thm_Erdos52_erdos_52
-- name    : Erdos52.erdos_52
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:41:46.256007+00:00
-- url     : https://prove2.me/theorems/587ac0e3-e774-4fc8-901f-9649291e53fa
-- title:
--   Erdős–Szemerédi sum–product conjecture
-- statement:
--   Let $A$ be a finite set of integers, with sumset $A+A=\{a+b : a,b\in A\}$ and product set $AA=\{ab : a,b\in A\}$. The Erdős–Szemerédi conjecture asserts that for every $\varepsilon$ with $0<\varepsilon<1$ there is a constant $C_\varepsilon>0$ such that for every finite $A\subset\mathbb Z$,
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C_\varepsilon\,|A|^{2-\varepsilon}.$$
--
--   This is the sharp form of the sum–product phenomenon: a finite set of integers cannot be simultaneously additively and multiplicatively structured.
--
--   **Formalization Note** This is the affirmative answer to Erdős Problem 52 as formalized in the Formal Conjectures project (where it appears as `answer(sorry) ↔ …`). Restricting to $\varepsilon<1$ loses nothing (the statement is monotone in $\varepsilon$) and keeps the exponent positive.
-- source:
--   https://www.erdosproblems.com/52 (conjecture as stated there)

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem erdos_52 : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by sorry
end Erdos52
