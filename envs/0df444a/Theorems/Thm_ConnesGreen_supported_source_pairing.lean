-- Prove2me | Theorems.Thm_ConnesGreen_supported_source_pairing
-- name    : ConnesGreen.supported_source_pairing
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T01:16:16.897896+00:00
-- url     : https://prove2.me/theorems/c6147961-53c2-4c4a-8a3b-54f5be2e70cb
-- title:
--   RG-3 — integrable same-representative Green pairing at Lg
-- statement:
--   For every $t>0$ and every smooth compactly supported test $g$ with closed support strictly inside $(-t,t)$, prove square integrability of $g,g'$ and $Lg$. For every actual critical-strip zero, prove integrability of the original Green product and equality of the physical inner product with $\int_{-t}^{t}\overline{F_{t,\rho}}Lg$. The physical representative is the source image of $Lg$, not the source image of $g$. The inner product is conjugate-linear in its first argument.
-- source:
--   Canonical Green mission specification RG-0 through RG-5, supplied in the proposal definition bundle and target statements. Original native formulas: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/DirichletResolvent.lean, DirichletEnergy.lean and ProblemOneIndependence.lean. Hilbert/Dirichlet background: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations (Springer 2011), https://doi.org/10.1007/978-0-387-70914-7. The canonical aggregate target is the explicit repository specification, not a quotation from the book or a claim of RH.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.supported_source_pairing (t : ℝ) (ht : 0 < t) : ConnesGreen.TestPairing t := by sorry
