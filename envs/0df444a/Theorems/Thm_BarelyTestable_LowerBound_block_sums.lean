-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_block_sums
-- name    : BarelyTestable.LowerBound.block_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:55.884777+00:00
-- url     : https://prove2.me/theorems/7ad999fe-be99-430d-9000-04fb73c272b0
-- title:
--   Claim 3.17 — exact and bounded block sums
-- statement:
--   For $m\ge4$, either prescribed block parity $\pi$, and each operation $j\in\{1,2,3\}$, the block counts satisfy
--
--   $$\sum_{U\subseteq A_i}s_j(U)^2=(1+1/m)m^4 2^{m-2},\qquad\sum_{U\subseteq A_i}t_j(U)\le(1+3/m)m^4 2^{m-3}.$$
--
--   The equality and inequality are both asserted. They control the separate first and second moments entering the load estimate.
--
--   Differences from the source:
--   - encoding: sums over subsets of block A_i, j ∈ {1,2,3} → subsets of Fin m, j ∈ Fin 3; reason: renaming the block and shifting operation indices changes no summand; m ≥ 4 makes both subtracted exponents nonnegative
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Claim 3.17, p. 23 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Claim 3.17, p.23: exact first sum and upper bound on the second. -/
theorem block_sums {m : ℕ} (hm : 4 ≤ m) (π : Bool) (j : Fin 3) :
    (∑ U : Cube (Fin m), (blockS j π U : ℝ)^2) =
      (1 + 1/(m : ℝ)) * (m : ℝ)^4 * 2^(m-2) ∧
    (∑ U : Cube (Fin m), (blockT j π U : ℝ)) ≤
      (1 + 3/(m : ℝ)) * (m : ℝ)^4 * 2^(m-3) := by sorry

end BarelyTestable.LowerBound
