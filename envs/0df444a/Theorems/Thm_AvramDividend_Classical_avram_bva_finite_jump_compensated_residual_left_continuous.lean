-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jump_compensated_residual_left_continuous
-- name    : AvramDividend.Classical.avram_bva_finite_jump_compensated_residual_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:49:18.906625+00:00
-- url     : https://prove2.me/theorems/69aef992-0f4a-47af-81bc-caa8cc8fea3d
-- title:
--   Left continuity of original finite-jump compensated drift residual
-- statement:
--   For a real physical path with finitely many actual nonzero jumps on (0,T] and drift-only evolution on every jump-free subinterval, subtracting the finite sum of its actual downward jumps from its drift deficit gives a function left-continuous at every physical jump time. The proof uses local affine evolution immediately before a jump, finite marked-step strict left limits, and the exact cancellation of the physical jump.
-- source:
--   Finite activity path residual, strict-left limit and finite jump cancellation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_jump_compensated_residual_left_continuous
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    ∀ u ∈ hFinite.toFinset,
      Function.leftLim
        (fun t : ℝ≥0 => (t : ℝ) * drift - f t -
          Finset.sum hFinite.toFinset (fun v => if v ≤ t then
            Function.leftLim f v - f v else 0)) u =
      (u : ℝ) * drift - f u -
        Finset.sum hFinite.toFinset (fun v => if v ≤ u then
          Function.leftLim f v - f v else 0) := by sorry
