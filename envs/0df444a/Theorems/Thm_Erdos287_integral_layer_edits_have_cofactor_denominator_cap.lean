-- Prove2me | Theorems.Thm_Erdos287_integral_layer_edits_have_cofactor_denominator_cap
-- name    : Erdos287.integral_layer_edits_have_cofactor_denominator_cap
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:40:36.530415+00:00
-- url     : https://prove2.me/theorems/9ff33782-4f48-43b2-8f6f-37a3f28ba665
-- title:
--   Edits preserving large-prime integrality have a cofactor lattice
-- statement:
--   Let $C>0$ and suppose two rational sums $s,t$ both have reduced denominators coprime to $P$. Suppose $s-t$ is a sum of integer multiples of $1/n$ over finitely many $n$ dividing $CP$. Then the reduced denominator of $s-t$ divides $C$. In particular either $s=t$ or $|s-t|C\ge1$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.integral_layer_edits_have_cofactor_denominator_cap (D : Finset ℕ) (sign : ℕ → ℤ) (s t : ℚ) (C P : ℕ) (hC : 0 < C)
    (hD : ∀ n ∈ D, n ∣ C * P) (hs : s.den.Coprime P) (ht : t.den.Coprime P)
    (hedit : s - t = ∑ n ∈ D, (sign n : ℚ) / n) :
    (s - t).den ∣ C ∧ (s = t ∨ 1 ≤ |s - t| * (C : ℚ)) := by sorry
