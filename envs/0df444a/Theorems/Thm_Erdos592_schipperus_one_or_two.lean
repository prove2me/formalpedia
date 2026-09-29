-- Prove2me | Theorems.Thm_Erdos592_schipperus_one_or_two
-- name    : Erdos592.schipperus_one_or_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:10:07.924886+00:00
-- url     : https://prove2.me/theorems/31c75db8-058f-4f87-87fa-c2bb7b52f75e
-- title:
--   Schipperus: $\omega^{\omega^\gamma}$ is a partition ordinal when $\gamma$ is a sum of one or two indecomposables
-- statement:
--   Let $\gamma$ be a countable ordinal which is the sum of one or two indecomposable ordinals, i.e. $\gamma=\omega^{\delta_1}$, or $\gamma=\omega^{\delta_1}+\omega^{\delta_2}$ with $\delta_1\ge\delta_2$. Then
--   $$\omega^{\omega^{\gamma}} \to \left(\omega^{\omega^{\gamma}}, 3\right)^2 .$$
--
--   This is the positive part of Schipperus's 2010 theorem on countable partition ordinals. It contains Chang's theorem ($\gamma=1$, giving $\omega^\omega$) and Erdős Problem 591 ($\gamma=2$, giving $\omega^{\omega^2}$).
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Schipperus [Sc10] (R. Schipperus, Countable partition ordinals, Ann. Pure Appl. Logic, 2010)

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem schipperus_one_or_two (γ : Ordinal.{u}) (hγ : γ.card ≤ ℵ₀)
    (h : IsSumOfIndecomposables 1 γ ∨ IsSumOfIndecomposables 2 γ) :
    OrdinalCardinalRamsey (ω ^ ω ^ γ) (ω ^ ω ^ γ) 3 := by sorry
end Erdos592
