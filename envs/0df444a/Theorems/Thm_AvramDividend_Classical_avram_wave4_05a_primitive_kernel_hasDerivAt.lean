-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_primitive_kernel_hasDerivAt
-- name    : AvramDividend.Classical.avram_wave4_05a_primitive_kernel_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:24:26.363119+00:00
-- url     : https://prove2.me/theorems/f8923544-ef15-4b85-a273-95e1944a9748
-- title:
--   Actual compensated-jump derivative for the unbounded-variation scale primitive
-- statement:
--   For the original spectrally negative Levy generator and q-scale W in the non-bounded-variation branch, U(z)=∫0..z W is differentiable everywhere with U'=W, including at the killed lower boundary. Under Standing, W is C1 at every positive reserve x. For every fixed jump y (including jumps whose shifted argument x+y crosses zero), the complete compensated source increment J_U(z,y)=U(z+y)-U(z)-U'(z)y 1_{-1<y<1} has derivative J_W(x,y) at x>0. This is the fixed-mark differentiation identity needed for a later local Fubini/dominated-convergence theorem differentiating the primitive generator; it does not assert that differentiation commutes with the Levy measure integral or any q-harmonicity.
-- source:
--   Avram Palmowski Pistorius 2007 Lemma 4 pure-jump generator calculation. Genuine source definitions, Proved P2 global unbounded-variation U'=W a9a01dd4, Proved C1 scale regularity 310bb0bc, and zero-origin continuity 3321ae26; pinned Mathlib intervalIntegral.integral_hasDerivAt_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05a_primitive_kernel_hasDerivAt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
        (fun v : ℝ => ∫ t in (0 : ℝ)..v, W t) z y)
      (SpectrallyNegativeLevy.generatorIntegrand W x y) x := by sorry
