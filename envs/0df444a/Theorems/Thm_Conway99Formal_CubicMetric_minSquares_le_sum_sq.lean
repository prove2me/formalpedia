-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_minSquares_le_sum_sq
-- name    : Conway99Formal.CubicMetric.minSquares_le_sum_sq
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:07:02.203999+00:00
-- url     : https://prove2.me/theorems/ea8cd65e-376c-4960-b800-9dd19bed3170
-- title:
--   Lower bound for integer square sums
-- statement:
--   For finite $S$ and integer coordinates summing to $n$, $\operatorname{minSquares}(|S|,n)\le\sum_{i\in S}x_i^2$. The sum condition is explicit; the set may be empty.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#12-47; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L12-L47.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.minSquares_le_sum_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℤ) (total : ℤ)
    (htotal : ∑ i ∈ s, x i = total) :
    minSquares s.card total ≤ ∑ i ∈ s, (x i) ^ 2 := by sorry
