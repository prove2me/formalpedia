-- Prove2me | Theorems.Thm_Erdos592_erdos_592_three_indecomposables
-- name    : Erdos592.erdos_592_three_indecomposables
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:02:01.148991+00:00
-- url     : https://prove2.me/theorems/c79cbe94-e34d-4ebc-82b9-375564c28f85
-- title:
--   Erdős 592, open case: $\omega^{\omega^\gamma}$ is a partition ordinal when $\gamma$ is a sum of three indecomposables
-- statement:
--   Let $\gamma$ be a countable ordinal which is the sum of exactly three indecomposable ordinals, i.e.
--   $$\gamma = \omega^{\delta_1}+\omega^{\delta_2}+\omega^{\delta_3},\qquad \delta_1\ge\delta_2\ge\delta_3 .$$
--   Then $\alpha=\omega^{\omega^{\gamma}}$ is a partition ordinal:
--   $$
--   \omega^{\omega^{\gamma}} \to \left(\omega^{\omega^{\gamma}},\, 3\right)^2 ,
--   $$
--   that is, every red/blue colouring of the edges of $K_\alpha$ contains a red $K_\alpha$ or a blue triangle.
--
--   Erdős Problem 592 asks for exactly which countable $\beta$ the ordinal $\omega^\beta$ is a partition ordinal. By Galvin–Larson, for $\beta\ge 3$ this forces $\beta=\omega^\gamma$; Schipperus settled the cases where $\gamma$ is a sum of one or two indecomposables (positively) and of four or more (negatively). The case of three indecomposables is the one that remains open, and this statement is its positive resolution, as predicted by the Galvin–Larson conjecture. A formal **disproof** of this statement (exhibiting such a $\gamma$ for which the partition relation fails) would be an equally significant resolution.
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; open case as described in the remarks on that page (Galvin–Larson conjecture restricted to γ a sum of three indecomposables)

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem erdos_592_three_indecomposables (γ : Ordinal.{u}) (hγ : γ.card ≤ ℵ₀)
    (h3 : IsSumOfIndecomposables 3 γ) :
    OrdinalCardinalRamsey (ω ^ ω ^ γ) (ω ^ ω ^ γ) 3 := by sorry
end Erdos592
