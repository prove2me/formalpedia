-- Prove2me | Theorems.Thm_BlockCycleRotation_bulk_pair_estimate
-- name    : BlockCycleRotation.bulk_pair_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:35.413075+00:00
-- url     : https://prove2.me/theorems/ae4f6e9c-300f-4e2b-be43-89af549b6d4e
-- title:
--   The estimate at one bulk coprime pair
-- statement:
--   For a bulk pair $a>a'\ge 1$ with $\gcd(a,a')=1$ and $d\,a(a+a') \le m$, the inner sum over $b'$ differs from
--   $$\frac{d\,m}{a+a'} + m^2\,c(a,a')$$
--   by at most an explicit multiple of $\bigl(da + 2m/a\bigr)(1+\log m)$.
--
--   This is where the main term $m^2 c(a,a')$ — the summand of the series defining $C$ — first appears: evaluating the inner sum in closed form produces it, and the deviation is exactly what Lemmas 16 and 18 bound.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L45-L169

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Finset Real

set_option maxHeartbeats 1000000 in
-- Three separate approximations are chained here, each with its own algebraic
-- normalisation; the default budget is not enough.

theorem BlockCycleRotation.bulk_pair_estimate {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hgcd : Nat.gcd a a' = 1)
    (hbulk : d * a * (a + a') ≤ m) :
    |((∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))|
      ≤ 2 * (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / (a : ℝ)) * (1 + Real.log m) := by sorry
