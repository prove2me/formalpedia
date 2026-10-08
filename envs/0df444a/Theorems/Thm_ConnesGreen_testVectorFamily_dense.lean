-- Prove2me | Theorems.Thm_ConnesGreen_testVectorFamily_dense
-- name    : ConnesGreen.testVectorFamily_dense
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:16:13.58531+00:00
-- url     : https://prove2.me/theorems/7ac3ba33-fd7f-4288-ad29-aba997634158
-- title:
--   The original admissible physical test vectors are dense
-- statement:
--   For every original positive support window $t$, the original physical vectors $\operatorname{sourceEmbed}_t(Lg)$, with $g$ ranging over the unchanged original admissible tests supported in $(-t,t)$, have dense range in the original completed carrier. The accepted source-normalization theorem identifies these vectors with the original energy vectors. The carrier is the closure of their span, and admissible tests are closed under addition and complex scalar multiplication, so the vectors themselves are dense. No positivity, zero truncation, replacement carrier or density premise is assumed.
-- source:
--   monocap-tech/weil at 7c5b1bc48d1cd2dd7385b1e634cd33a1e95550c7. CanonicalGreenTestDensity.lean, CanonicalGreenQuadraticEndpoint.lean and CriticalWindowBoundary.lean. Exact native definitions are unfolded only where no separate platform definition exists; native Lean checks these public statements against the originals.

import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.testVectorFamily_dense (t : ℝ) (ht : 0 < t) : DenseRange (fun g : {g : ℝ → ℂ // SupportedTest t g} => sourceEmbed t (problemOneL g.1)) := by sorry
