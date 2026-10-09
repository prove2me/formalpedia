-- Prove2me | Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
-- name    : ConnesGreen.canonicalPositiveCovariance_compact
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T05:53:41.052085+00:00
-- url     : https://prove2.me/theorems/d7a10ac6-f611-4804-babe-a52655329911
-- title:
--   The original full positive covariance is compact
-- statement:
--   For every original positive support window, the complete actual-positive covariance $PP^*$ on the original completed physical carrier is compact. Its finite original positive-covariance approximations converge in operator norm, with error bounded by the COMPLETE sum of squared norms of all omitted original positive columns. Actual zero multiplicities and the physical metric are unchanged; no surrogate zero set is used.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdSpectrum.lean, exact declaration ConnesGreen.canonicalPositiveCovariance_compact, compiling source ab20377e04b8056e6db154b7054f60e0ce0a8f00

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus

theorem ConnesGreen.canonicalPositiveCovariance_compact (t : ℝ) (ht : 0 < t) :
    IsCompactOperator (canonicalPositiveCovariance t ht) := by sorry
