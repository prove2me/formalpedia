-- Prove2me | Theorems.Thm_ConstrSOSP_fGrid_contDiff
-- name    : ConstrSOSP.fGrid_contDiff
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:38.516445+00:00
-- url     : https://prove2.me/theorems/f6611d9d-672c-43b8-bc78-c7cec0820137
-- title:
--   The constructed function $f$ is $C^2$
-- statement:
--   Let $C$ be a well-formed Iter circuit and $f$ the piecewise biquintic function of the reduction on $[0,N]^2$, $N=6\cdot2^n+6$.
--
--   **Theorem.** $f$ is twice continuously differentiable.
--
--   On a common edge of two cells the two polynomials are determined by the same corner data and agree, so the interpolation has zero-, first- and second-order continuity across $[0,N]^2$. Every later step (Lipschitz constants, Taylor promises, stationarity) needs this.
--
--   Differences from the source:
--   - generalization: C² continuity across the whole domain [0, N]² → C² on all of ℝ² for the function that continues the boundary cells' polynomials outside [0, N]²; reason: the extension is part of the Lean definition only; the statement restricts to the paper's on a neighbourhood of [0, N]²
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.2, p.24

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_fGrid

namespace ConstrSOSP

/-- **The constructed function is `C²`** (arXiv:2604.02285, 2 Nov 2026, §5.2, p.24: "Now, it is
easy to see that the resulting polynomials of two adjacent small boxes on the common edge are
uniquely determined by the corner constraints and are equal, since the constraints are the same.
Therefore, our biquintic interpolation satisfies zero-order, first-order and second-order
continuity across the whole domain [0, N]^2.").

For every well-formed Iter circuit `C`, the piecewise biquintic function `f = fGrid C` is twice
continuously differentiable.

**Formalization Note** `fGrid C` continues the polynomials of the boundary cells outside
`[0, N]²`, so the statement is `C²` on the whole plane; its restriction to a neighbourhood of
`[0, N]²` is the paper's claim. -/
theorem fGrid_contDiff (C : Circuit) (hC : C.WF) : ContDiff ℝ 2 (fGrid C) := by sorry

end ConstrSOSP
