-- Prove2me | Theorems.Thm_BlockCycleRotation_relation
-- name    : BlockCycleRotation.relation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:35.642263+00:00
-- url     : https://prove2.me/theorems/c4ddf277-0b9e-462e-85d1-d7072d0cfd96
-- title:
--   Equation (relation): $M(n,k) = n f(k/n) - \gcd(n,k)$
-- statement:
--   For $0 < n$ and $k \le n$,
--   $$\operatorname{algCost}(n,k) + \gcd(n,k) = n\, f\!\left(\frac{k}{n}\right),$$
--   where $f = 1 + \psi$ is the normalised cost function on $[0,1]$.
--
--   This is the paper's equation (relation). It converts every statement about the algorithm's move count into a statement about the value of a fixed real function at a rational point, which is what makes the Riemann-sum argument of Theorem 9 possible.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L336-L352

import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.relation {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) + ((Nat.gcd n k : ℕ) : ℝ)
      = (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)) := by sorry
