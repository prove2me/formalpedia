-- Prove2me | Theorems.Thm_ConnesGreen_canonical_Green_realization_and_synthesis
-- name    : ConnesGreen.canonical_Green_realization_and_synthesis
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T01:17:53.455026+00:00
-- url     : https://prove2.me/theorems/e3b8ee7b-5865-4eab-8e59-a05f24062323
-- title:
--   RG-0 — canonical actual-zero Green realization and bounded synthesis
-- statement:
--   For every positive radius $t$, use the specified closed energy-image completion $H_t$ and its fixed Riesz source map. Prove dense source-lift range; square integrability, membership and exact source/Green energy-vector identification for every actual critical-strip zeta zero; the original source norm and supported $Lg$ Green pairing identities; and full multiplicity-weighted energy summability with bounded actual-zero synthesis, summable vector series, exact basis columns, exact adjoint coordinates and energy, the quantitative operator bound and uniqueness. No physical norm or pairing identity, column summability, RH, positivity or separation statement is assumed. The goal concerns the chosen window carrier, not a common carrier for all windows or a prescribed-window negative witness.
-- source:
--   Canonical Green mission specification RG-0 through RG-5, supplied in the proposal definition bundle and target statements. Original native formulas: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/DirichletResolvent.lean, DirichletEnergy.lean and ProblemOneIndependence.lean. Hilbert/Dirichlet background: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations (Springer 2011), https://doi.org/10.1007/978-0-387-70914-7. The canonical aggregate target is the explicit repository specification, not a quotation from the book or a claim of RH.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.canonical_Green_realization_and_synthesis (t : ℝ) (ht : 0 < t) : DenseRange (ConnesGreen.sourceLift t) ∧ ConnesGreen.ColumnRealization t ∧ ConnesGreen.TestPairing t ∧ ConnesGreen.RawSynthesis t := by sorry
