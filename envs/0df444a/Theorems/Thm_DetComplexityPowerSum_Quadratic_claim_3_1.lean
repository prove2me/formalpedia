-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_1
-- name    : DetComplexityPowerSum.Quadratic.claim_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:41.196548+00:00
-- url     : https://prove2.me/theorems/606a7c5f-1235-4061-93bc-08bb56f70a2b
-- title:
--   Claim 3.1 — the polar slice is finite with at least $(n-1)^{n-2}$ points
-- statement:
--   Let $n\ge 2$ and let $S\subseteq\mathbb C^n$ be the set of solutions of the system of Definition 2.2. Then $S$ is finite and
--   $$|S|\ge (n-1)^{n-2}.$$
--
--   The size counts distinct complex points. This is the lower bound on the original system, and it is what the determinantal upper bound is compared with.
--
--   **Formalization Note** Finiteness is an explicit conclusion, since `Set.ncard` is $0$ on an infinite set.
--
--   Differences from the source:
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 5, Claim 3.1

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_PolarSlice
open MvPolynomial

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_1 {n : ℕ} (hn : 2 ≤ n) :
    (polarSlice n).Finite ∧ (n - 1) ^ (n - 2) ≤ (polarSlice n).ncard := by sorry

end DetComplexityPowerSum.Quadratic
