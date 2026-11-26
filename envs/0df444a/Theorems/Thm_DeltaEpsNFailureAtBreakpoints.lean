-- Prove2me | Theorems.Thm_DeltaEpsNFailureAtBreakpoints
-- name    : DeltaEpsNFailureAtBreakpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:15.943368+00:00
-- url     : https://prove2.me/theorems/9d5b3464-4d35-5c27-beac-393591c2604b
-- title:
--   Delta Eps NFailure At Breakpoints: Delta Eps NFailure At Breakpoints
-- statement:
--   If a closed piecewise-geodesic curve `γ` fails to be a `(δ,ε,n)`-curve, then a minimizing
--   geodesic resolution of `γ` (\noderef{smallPieceCount}-attaining, hence strictly monotone by
--   `MinimizingResolutionStrict`) has two breakpoints `s p ≠ s q` such that the index window between
--   them (in either the ordinary or wrap-around sense, matching `BasicCutResolutionAtBreakpoints`'s
--   `inArc` predicate) contains exactly `n + 1` small edges, at most `2 * ε⁻¹ + (n + 1)` edges in
--   total, and has arc length (in the same ordinary-or-wrap sense) at most `2 * ε⁻¹ * δ`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DeltaEpsNFailureAtBreakpoints.lean#L15-L454
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DeltaEpsNFailureAtBreakpoints.lean#L15-L454

import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_MinimizingResolutionStrict
import Definitions.Def_Tablet_BigEdgeWindowPacking
import Definitions.Def_Tablet_DeltaEpsNFailureAtBreakpoints
import Theorems.Thm_BigEdgeWindowPacking
import Theorems.Thm_MinimizingResolutionStrict

set_option autoImplicit false
open Set

theorem DeltaEpsNFailureAtBreakpoints {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (n : ℕ) (hfail : ¬ IsDeltaEpsN γ δ ε n) :
    ∃ (k : ℕ) (s : ℕ → ℝ) (p q : ℕ),
      IsGeodesicResolution γ k s ∧
      ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card = smallPieceCount γ δ ∧
      StrictMonoOn s (Set.Icc 0 k) ∧
      p ≤ k ∧ q ≤ k ∧ s p ≠ s q ∧
      ((Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)).card = n + 1 ∧
      (((Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card : ℝ)
        ≤ 2 * ε⁻¹ + ((n : ℝ) + 1) ∧
      (if p < q then s q - s p else (γ.len - s p) + s q) ≤ 2 * ε⁻¹ * δ := by sorry
