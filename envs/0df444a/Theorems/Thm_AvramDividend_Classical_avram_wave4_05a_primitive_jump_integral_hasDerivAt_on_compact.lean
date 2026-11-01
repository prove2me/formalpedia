-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
-- name    : AvramDividend.Classical.avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:33:09.386559+00:00
-- url     : https://prove2.me/theorems/5557edc6-6c2e-4c35-b185-7b76b7a8444d
-- title:
--   Local derivative commutation for the actual compensated Lévy integral of the scale primitive
-- statement:
--   Let U(z)=∫0..z W be the true unbounded-variation q-scale primitive. On a compact reserve interval [l,u] strictly within the positive C2 region (0,a) of W, the map z↦∫_{y<0} generatorIntegrand U z y ν(dy) has the derivative ∫_{y<0} generatorIntegrand W x y ν(dy) for every x∈(l,u). This is full differentiation under the original source Lévy measure, not just fixed-jump differentiation. It uses the genuine ν quadratic moment, P3's compact uniform C min(1,y²) domination for both U and W, source monotonicity and measurability, and a pinned Mathlib local dominated parameter-integral derivative theorem. It is independent of generator harmonicity, primitive Laplace identity, hFubini premises, or the Open P2 parent. It supplies the missing analytic jump-integral commutation for the pure σ=0 branch, after which only elementary drift/discount differentiation remains to obtain d[(Γ-q)U]/dx=(Γ-q)W.
-- source:
--   Avram Palmowski Pistorius 2007 Lemma 4 source generator calculation; P2 canonically Proved global primitive derivative a9a01dd4, C2 primitive 925aaf62 and global monotonicity 226a1286; P3 Proved uniform quadratic bound c9a18a64; new 05-A exact fixed-mark derivative f8923544 (publication already canonical); pinned Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le and Lévy ν_integrable. Full 192-line combined private proof reached compiler sentinel with zero candidate diagnostics, job 4ddb6217-0f87-4163-8360-683cc81147b8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (x : ℝ) (hx : x ∈ Ioo l u) :
    HasDerivAt
      (fun z : ℝ => ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun v : ℝ => ∫ t in (0 : ℝ)..v, W t) z y ∂X.ν)
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) x := by sorry
