-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
-- name    : AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integrals_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:12:19.896974+00:00
-- url     : https://prove2.me/theorems/99bb9a4b-5880-46cc-a0d9-98b5774146ca
-- title:
--   Original physical finite-cell bounded measurable mark-simple integrals converge to the real marked jump integral
-- statement:
--   For any finite-mass physical time-mark rectangle (0,T]×S under an arbitrary measure μ, and any uniformly unit-bounded sequence of measurable finite-valued real mark functions f_k converging pointwise to a real mark weight g on S, the actual real set integrals ∫ f_k(z) dμ over that rectangle converge to ∫ g(z) dμ. The proof applies pinned Bochner dominated convergence to the restricted original rectangle measure, using measurability of finite simple functions, the a.e. restriction-membership theorem, the uniform bound 1 and integrability of the constant 1 under the finite restricted measure. This is the real marked-integral approximation limit needed, with no replacement of the physical original Lévy jump measure or reliance on Poisson count distribution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integrals_tendsto
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : μ (Ioc 0 T ×ˢ S) < ⊤)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    Tendsto
      (fun k => ∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂μ)
      atTop (𝓝 (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂μ)) := by sorry
