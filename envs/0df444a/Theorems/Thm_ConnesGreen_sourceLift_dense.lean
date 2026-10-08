-- Prove2me | Theorems.Thm_ConnesGreen_sourceLift_dense
-- name    : ConnesGreen.sourceLift_dense
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T01:14:43.995172+00:00
-- url     : https://prove2.me/theorems/86074cca-f1aa-4216-9b89-dad34588a9b5
-- title:
--   RG-1 — dense image of the canonical L2 source lift
-- statement:
--   For every $t>0$, the projection of the loads $(0,2f)$, with $f$ ranging over all of $L^2([-t,t];\mathbb C)$, has dense range in the specified closure of the energy images of supported smooth tests. The conclusion is density rather than surjectivity; it identifies the completion reached by the original source map without postulating an arbitrary Hilbert carrier.
-- source:
--   Canonical Green mission specification RG-0 through RG-5, supplied in the proposal definition bundle and target statements. Original native formulas: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/DirichletResolvent.lean, DirichletEnergy.lean and ProblemOneIndependence.lean. Hilbert/Dirichlet background: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations (Springer 2011), https://doi.org/10.1007/978-0-387-70914-7. The canonical aggregate target is the explicit repository specification, not a quotation from the book or a claim of RH.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.sourceLift_dense (t : ℝ) (ht : 0 < t) : DenseRange (ConnesGreen.sourceLift t) := by sorry
