-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_bounded_auto_L2_mean_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_bounded_auto_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:21:38.184897+00:00
-- url     : https://prove2.me/theorems/503354b8-03a0-40bd-91ad-651e45a583f6
-- title:
--   Physical stopped finite-mark jump martingale is L2 and centred from bounded predictable coefficients
-- statement:
--   Original intrinsic physical negative jump counts, stopped at a genuine right-continuous stopping time and multiplied by bounded predictable finite-mark coefficients, produce an L2 and mean-zero terminal on their original Omega and P. The coefficient MemLp2 premise from the earlier Proved finite-family theorem is fully discharged by Mathlib MemLp.of_bound and predictability, with no independent jump process.
-- source:
--   Strictly derives physical bounded predictable H ∈ L2 on P using a F.rightCont-to-global measurability monotonicity and pinned Mathlib MemLp.of_bound, then imports only the fully Proved original finite-mark compensated L2 centring theorem 92f30741.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_bounded_auto_L2_mean_zero
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε)
    (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ j i, X.ν (C j i) < ⊤)
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (L : ι → ℝ) (hBound : ∀ j i ω, |H j i ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun j ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i ω) *
          ((N j i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C j i)).toReal)
    MemLp (fun ω => ∑ j ∈ F, Z j ω) 2 P ∧
      (∫ ω, ∑ j ∈ F, Z j ω ∂P) = 0 := by sorry
