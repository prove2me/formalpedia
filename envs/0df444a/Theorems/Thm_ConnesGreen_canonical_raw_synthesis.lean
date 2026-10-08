-- Prove2me | Theorems.Thm_ConnesGreen_canonical_raw_synthesis
-- name    : ConnesGreen.canonical_raw_synthesis
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T01:17:15.904081+00:00
-- url     : https://prove2.me/theorems/a78c3633-3464-4a53-88c9-656ff7cf8eee
-- title:
--   RG-5 — exact-column canonical raw synthesis and adjoint energy
-- statement:
--   For every $t>0$, prove full weighted-energy summability and construct a bounded complex-linear map from square-summable coefficients on the complete actual-zero subtype to the specified physical carrier. Its columns are exactly $\sqrt{m_\rho}$ times the fixed source images. Require summability of every synthesis vector family, the exact series formula, original basis columns, adjoint coordinate and squared-norm formulas, the total-energy operator bound, and uniqueness among bounded maps on the same carrier with the same columns. The physical carrier and source map are computed definitions, not free inputs.
-- source:
--   Canonical Green mission specification RG-0 through RG-5, supplied in the proposal definition bundle and target statements. Original native formulas: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/DirichletResolvent.lean, DirichletEnergy.lean and ProblemOneIndependence.lean. Hilbert/Dirichlet background: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations (Springer 2011), https://doi.org/10.1007/978-0-387-70914-7. The canonical aggregate target is the explicit repository specification, not a quotation from the book or a claim of RH.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.canonical_raw_synthesis (t : ℝ) (ht : 0 < t) : ConnesGreen.RawSynthesis t := by sorry
