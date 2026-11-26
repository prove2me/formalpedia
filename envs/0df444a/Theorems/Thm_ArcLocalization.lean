-- Prove2me | Theorems.Thm_ArcLocalization
-- name    : ArcLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:35.079487+00:00
-- url     : https://prove2.me/theorems/77abcf91-c350-4416-94e2-85cf7e85f8fa
-- title:
--   Arc Localization: Arc Localization
-- statement:
--   Interval localization of a circle-distance ball. If `u ∈ [0, γ.len]`, `ρ > 0` and
--   `2ρ < γ.len`, then the sublevel set `I = {v ∈ [0,γ.len] : d_γ(u,v) < ρ}` is contained either in a
--   genuine subinterval `[t,t']` of `[0,γ.len]` of length at most `2ρ`, or — when `γ` is closed — in a
--   wrap-around arc `[t,γ.len] ∪ [0,t']` of total length at most `2ρ`. In each case the endpoints that
--   are not clamped to `0` or `γ.len` are at circle distance exactly `ρ` from `u`, hence lie outside
--   `I`. This is Step 2 (and the endpoint computation of Step 4) of paper Lemma 3.7's proof
--   (paper.tex line 762), which the paper leaves implicit.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcLocalization.lean#L13-L109
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcLocalization.lean#L13-L109

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_ArcLocalization
set_option autoImplicit false
open Set

theorem ArcLocalization {E : Type*} [MetricSpace E] (γ : Curve E) (u ρ : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) γ.len) (hρ : 0 < ρ) (hlen : 2 * ρ < γ.len) :
    (∃ t t' : ℝ, 0 ≤ t ∧ t ≤ t' ∧ t' ≤ γ.len ∧ t' - t ≤ 2 * ρ ∧
        { v ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ u v < ρ } ⊆ Set.Icc t t' ∧
        (t = 0 ∨ dGamma γ u t = ρ) ∧ (t' = γ.len ∨ dGamma γ u t' = ρ)) ∨
      (IsClosedCurve γ ∧ ∃ t t' : ℝ, 0 ≤ t' ∧ t' < t ∧ t ≤ γ.len ∧
        (γ.len - t) + t' ≤ 2 * ρ ∧
        { v ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ u v < ρ } ⊆
          Set.Icc t γ.len ∪ Set.Icc 0 t' ∧
        dGamma γ u t = ρ ∧ dGamma γ u t' = ρ) := by sorry
