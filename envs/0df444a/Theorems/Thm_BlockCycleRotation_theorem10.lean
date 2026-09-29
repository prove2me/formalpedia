-- Prove2me | Theorems.Thm_BlockCycleRotation_theorem10
-- name    : BlockCycleRotation.theorem10
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:06.334388+00:00
-- url     : https://prove2.me/theorems/d9da038b-68ca-48e1-bba9-4dfe74da9708
-- title:
--   Theorem 9: the average cost converges to $2\int_0^{1/2} f$
-- statement:
--   $$\frac{\operatorname{avgCost}(n)}{n} \longrightarrow 2\int_0^{1/2} f(x)\,dx \qquad (n \to \infty).$$
--
--   Theorem 9. By equation (relation) the average of the algorithm's cost over all shifts of an array of length $n$ is an equally spaced Riemann sum for $f$, up to the $\gcd$ correction $\sum_{k<n}\gcd(n,k) = o(n^2)$. Theorem 7 supplies the Riemann integrability that makes those sums converge, and the symmetry $f(1-x)=f(x)$ folds the integral onto $[0,\tfrac12]$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 9. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L1078-L1085

import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.theorem10 :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop
      (𝓝 (2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x)) := by sorry
