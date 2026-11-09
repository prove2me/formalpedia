-- Prove2me | Theorems.Thm_CondGeoVerif_eq_2_2
-- name    : CondGeoVerif.eq_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:26:47.066483+00:00
-- url     : https://prove2.me/theorems/3f1172c4-f89f-4cc0-aee3-91ea5616cc95
-- title:
--   (2.2) — paired-loss identity $R(h_v)-R(h_w)=\mathbb E[(2E_v-1)D_{v,w}]$
-- statement:
--   Let $P$ be a law of $(X,Y)\in\mathbb R^d\times\{-1,1\}$ with arbitrary labels, and let $h_v,h_w$ be measurable predictors. With $E_v=\mathbf 1\{Y\ne h_v(X)\}$ and $D_{v,w}=\mathbf 1\{h_v(X)\ne h_w(X)\}$,
--   $$R(h_v)-R(h_w)=\mathbb E\big[(2E_v-1)D_{v,w}\big].\qquad(2.2)$$
--   This identity underlies both the upper certificates and the improving alternatives of the lower bounds.
--
--   Differences from the source:
--   - generalization: laws with Gaussian feature marginal and projection predictors h_v, h_w → every probability law on ℝᵈ × {−1,1} and every pair of measurable predictors; reason: the identity holds pointwise in (X, Y); the paper's setting is a special case
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2, p.4 (PDF p.7), eq. (2.2)

import Mathlib
import Definitions.Def_CondGeoVerif_risk
import Definitions.Def_CondGeoVerif_Mprog

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **The paired-loss identity (2.2)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §2, p.4 = PDF p.7): with
`E_v = 1{Y ≠ h_v(X)}` and `D_{v,w} = 1{h_v(X) ≠ h_w(X)}`, arbitrary labels satisfy
`R(h_v) − R(h_w) = E[(2E_v − 1)D_{v,w}]`.

**Formalization Note** Stated for every probability law of `(X, Y)` and every pair of measurable
predictors; the paper's predictors are projection rules under a Gaussian feature marginal. -/
theorem eq_2_2 {d : ℕ} (P : Measure (Vec d × Bool)) [IsProbabilityMeasure P]
    (hv hw : Vec d → Bool) (hhv : Measurable hv) (hhw : Measurable hw) :
    risk P hv - risk P hw =
      ∫ p, (2 * ind (decide (hv p.1 ≠ p.2)) - 1) * ind (decide (hv p.1 ≠ hw p.1)) ∂P := by sorry

end CondGeoVerif
