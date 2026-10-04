-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_minSquares_attained
-- name    : Conway99Formal.CubicMetric.minSquares_attained
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:06:47.417841+00:00
-- url     : https://prove2.me/theorems/0eec44aa-554c-4829-a0e0-8f6259aec85e
-- title:
--   Attainment of the minimum square sum
-- statement:
--   For a finite nonempty set $S$ and integer total $n$, integer coordinates attain the Euclidean-division bound: $\sum_{i\in S}x_i=n$ and $\sum_{i\in S}x_i^2=\operatorname{minSquares}(|S|,n)$. Nonemptiness is the only premise.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#74-101; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L74-L101.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.minSquares_attained {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (total : ℤ) (hs : s.Nonempty) :
    ∃ x : ι → ℤ,
      (∑ i ∈ s, x i) = total ∧
      (∑ i ∈ s, (x i) ^ 2) = minSquares s.card total := by sorry
