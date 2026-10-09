-- Prove2me | Theorems.Thm_ConnesGreen_prime_convolution_overlap_mass_bound
-- name    : ConnesGreen.prime_convolution_overlap_mass_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:00:23.047727+00:00
-- url     : https://prove2.me/theorems/b824a892-b6e4-47f6-92cc-6117f6fe4ee0
-- title:
--   Complete prime contribution bounded by the termwise mass and overlap loss
-- statement:
--   Let $g$ be an original smooth compact complex test supported in $[-T,T]$, and set $h=g*g^*$ with $g^*(t)=\overline{g(-t)}$. For the original finite active prime-power set $A_T$ and physical mass and energy $M(g),E(g)$, define $$L_T(g)=\sum_{n\in A_T}\frac{2\Lambda(n)}{\sqrt n}\min(M(g),2E(g)\max(2T-\log n,0)).$$ Then the COMPLETE original prime contribution satisfies $$|\operatorname{Prime}(h)|\le L_T(g).$$ The choice between mass and energy is made separately at each prime power, retaining its actual support overlap. This does not assert positivity of the Weil form or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PrimeOverlapMass.lean, exact declaration ConnesGreen.prime_convolution_overlap_mass_bound, compiling local source 495a9f34f25d1dbfbeb6ba8dce6d4735559ae878. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_prime_overlap_loss
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen

theorem ConnesGreen.prime_convolution_overlap_mass_bound (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖primeSum (conv g (starInv g))‖ ≤ primeOverlapLoss T g := by sorry
