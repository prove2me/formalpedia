-- Prove2me | Theorems.Thm_ConnesGreen_convolution_overlap_dirichlet_energy_bound
-- name    : ConnesGreen.convolution_overlap_dirichlet_energy_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T19:14:51.274752+00:00
-- url     : https://prove2.me/theorems/29d00d91-1958-4996-843d-b918779126d0
-- title:
--   Shrinking convolution overlap is uniformly bounded in the original Dirichlet energy
-- statement:
--   For every original smooth test $g$ supported strictly inside $(-T,T)$, write $E(g)=\int|g\prime|^2+\tfrac14\int|g|^2$. For every real $x$, $$|(g\star g^*)(x)|\le2E(g)\max(2T-|x|,0).$$ This is the original Dirichlet energy, independently identified with the physical source norm squared in the native Green development. The estimate is uniform over moving tests and includes equality at the support boundary. It controls the prime-threshold overlap contribution, not the complete Weil quadratic form or actual-zero neutral-shell persistence.
-- source:
--   monocap-tech/weil, Connes/PrimeThresholdEnergy.lean. Original Connes supported-test, convolution and involution definitions. Native companion theorems prove a uniform relative-energy bound for the entire nearby prime-threshold remainder, preserving actual zero actors and selected packet.
--
--   Literature/source audit addendum (2026-10-11; COR-13): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil 475cc0a33fcc47f1e5f7d6d52108064cae6a32b8, WeilDefect/Connes/PrimeThresholdEnergy.lean, SHA256 d8979d93cb54db2734606034e45ca0e6299853988be57482f78e4024d233cd84. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace
noncomputable section

theorem ConnesGreen.convolution_overlap_dirichlet_energy_bound (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (x : ℝ) :
    ‖conv g (starInv g) x‖ ≤
      2 * ((∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2) +
        (1 / 4 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2)) * max (2 * T - |x|) 0 := by sorry
