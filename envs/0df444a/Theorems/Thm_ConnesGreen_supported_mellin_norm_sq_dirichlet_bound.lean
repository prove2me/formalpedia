-- Prove2me | Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_dirichlet_bound
-- name    : ConnesGreen.supported_mellin_norm_sq_dirichlet_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T19:33:54.386883+00:00
-- url     : https://prove2.me/theorems/534597f0-a18a-4ce6-8cf2-d6a01314a6cd
-- title:
--   Original Dirichlet energy uniformly bounds the Mellin transform on vertical strips
-- statement:
--   Let $T\ge0$ and let $g$ be an original smooth compactly supported Connes test with support strictly inside $(-T,T)$. Write $E(g)=\int_{\mathbb R}|g\prime(t)|^2\,dt+\tfrac14\int_{\mathbb R}|g(t)|^2\,dt$ and $\widehat g(z)=\int g(t)e^{(z-1/2)t}\,dt$. For every $z\in\mathbb C$, $$|\widehat g(z)|^2\le8T^2e^{2T|\operatorname{Re}z-1/2|}E(g).$$ The constant is independent of the imaginary part and the choice of test. This original-energy estimate controls the pole evaluations in the Weil distribution; it does not establish positivity of the pole pair or the full Weil form.
-- source:
--   monocap-tech/weil, Connes/NonArchimedeanEnergy.lean. Original SupportedTest, Mellin normalization and global Dirichlet integrals are preserved. Native companion results bound the complete pole-plus-prime component in the original physical source norm and isolate the remaining archimedean term.
--
--   Literature/source audit addendum (2026-10-11; COR-13): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil adc12a8dd32542a401991b65dfc3cf893d00d853, WeilDefect/Connes/NonArchimedeanEnergy.lean, SHA256 b7edb9d3864298c138b19a60f9a75fb7cae3434233cbb4f59fc7224f1fe0263a. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace
noncomputable section

theorem ConnesGreen.supported_mellin_norm_sq_dirichlet_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) (z : ℂ) :
    ‖mellinHat g z‖ ^ 2 ≤
      8 * T ^ 2 * Real.exp (2 * |z.re - 1 / 2| * T) *
        ((∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2) +
          (1 / 4 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2)) := by sorry
