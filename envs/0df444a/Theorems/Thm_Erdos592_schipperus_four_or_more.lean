-- Prove2me | Theorems.Thm_Erdos592_schipperus_four_or_more
-- name    : Erdos592.schipperus_four_or_more
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:11:09.206493+00:00
-- url     : https://prove2.me/theorems/9b632d32-a698-49f8-8bcb-5493f5b5fee1
-- title:
--   Schipperus: $\omega^{\omega^\gamma}$ is not a partition ordinal when $\gamma$ is a sum of four or more indecomposables
-- statement:
--   Let $k\ge 4$ be a natural number and let $\gamma$ be a countable ordinal which is the sum of exactly $k$ indecomposable ordinals, $\gamma=\omega^{\delta_1}+\cdots+\omega^{\delta_k}$ with $\delta_1\ge\cdots\ge\delta_k$. Then
--   $$\omega^{\omega^{\gamma}} \not\to \left(\omega^{\omega^{\gamma}}, 3\right)^2 .$$
--
--   This is the negative part of Schipperus's 2010 theorem. It shows in particular that the Galvin–Larson conjecture (every $\beta=\omega^\gamma\ge3$ has the property) fails, e.g. for $\gamma=4$.
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Schipperus [Sc10] (R. Schipperus, Countable partition ordinals, Ann. Pure Appl. Logic, 2010)

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem schipperus_four_or_more (γ : Ordinal.{u}) (hγ : γ.card ≤ ℵ₀) (k : ℕ) (hk : 4 ≤ k)
    (h : IsSumOfIndecomposables k γ) :
    ¬ OrdinalCardinalRamsey (ω ^ ω ^ γ) (ω ^ ω ^ γ) 3 := by sorry
end Erdos592
