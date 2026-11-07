-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_intrinsic_one_step_transform_factor
-- name    : AvramDividend.Classical.avram_bv_jump8_intrinsic_one_step_transform_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T13:51:29.829551+00:00
-- url     : https://prove2.me/theorems/d73fbe4f-0dc8-4daf-801a-0c2a79be376d
-- title:
--   Original intrinsic marked-jump Laplace transform factorises across one adjacent integer window
-- statement:
--   Let L(n,k) be the exact original-process marked-jump exponential expectation over (0,n] and strict negative cutoff mark<-1/(k+1). This theorem requires L(n+1,k)=L(n,k)L(1,k). Its proof must establish actual weighted source marked-increment measurability, future-past independence, and stationary law, with no time-zero atom; it isolates the genuine stochastic input for the integer-horizon power theorem.
-- source:
--   Use the verified half-open marked integral split across (0,n] and (n,n+1], finite cutoff almost-sure finiteness for ENNReal.toReal_add, exponential multiplication, and original process-independent stationary weighted marked increments. Do not infer the factorisation from mere count-means or from abstract non-source PRM.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_intrinsic_one_step_transform_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    let L : ℕ → ℕ → ℝ := fun n k => (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P);
    ∀ (n k : ℕ), L (n + 1) k = L n k * L 1 k := by sorry
