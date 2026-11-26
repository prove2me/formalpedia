-- Prove2me | Theorems.Thm_ArcDeltaEpsNCount
-- name    : ArcDeltaEpsNCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:25.20209+00:00
-- url     : https://prove2.me/theorems/81d1042f-c272-4c95-8c01-c40a94cf69c1
-- title:
--   Arc Delta Eps NCount: Arc Delta Eps NCount
-- statement:
--   A window of the circular arc `γ|_{[t,t']}` (`curveArc`) that avoids its (up to two) truncated
--   end edges pulls back, along the arc's own parametrization, to a circular window of `γ` of the same
--   length: if `γ` is a `(δ,ε,n)`-curve witnessed by `(k,s)`, and `(kA,sA)` is `γ|_{[t,t']}`'s named
--   geodesic resolution with the correspondence data of `ArcGeodesicResolution` (its interior
--   breakpoints, indices `1,…,kA-1`, genuine shifted breakpoints of `s`, split at `m` in the wrap
--   case, with the split point itself, `s(j0+(m-1))`, landing exactly on `γ.len` — the fact that makes
--   the tail and head correspondences meet at a single, genuine edge of `γ` rather than leaving a gap),
--   then the sub-window of the arc strictly between its own breakpoints `sA 1` and `sA (kA-1)` is
--   again a `(δ,ε,n)`-curve, provided that sub-window is non-closed (discharging `IsDeltaEpsN`'s wrap
--   clause vacuously, as in `RestrictDeltaEpsNAtBreakpoints`). This is the only consumer anywhere in
--   the tablet of `IsDeltaEpsN`'s second (wrap) counting clause: a window straddling the arc's own
--   wrap point pulls back to a circular window of `γ`, handled by that clause.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcDeltaEpsNCount.lean#L24-L235
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcDeltaEpsNCount.lean#L24-L235

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ClampedLinearShortEdgeCount
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_ArcDeltaEpsNCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ClampedLinearShortEdgeCount
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set

theorem ArcDeltaEpsNCount {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
    (hlin : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ γ.len → b - a ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n)
    (hwrap : ∀ a b : ℝ, 0 ≤ b → b < a → a ≤ γ.len → (γ.len - a) + b ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => (a ≤ s (j - 1) ∨ s j ≤ b) ∧ s j - s (j - 1) < δ)).card ≤ n)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len)
    (kA : ℕ) (sA : ℕ → ℝ) (hkA : 1 ≤ kA)
    (hresA : IsGeodesicResolution (curveArc γ hcl t t' ht0 htl ht'0 ht'l) kA sA)
    (hord : t ≤ t' → ∃ j0 : ℕ,
        ∀ i : ℕ, 1 ≤ i → i ≤ kA - 1 → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t)
    (hwr : t' < t → ∃ j0 m : ℕ,
        (∀ i : ℕ, 1 ≤ i → i ≤ m → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
        (∀ i : ℕ, m < i → i ≤ kA - 1 → i - m ≤ k ∧
          sA i = (γ.len - t) + s (i - m)) ∧
        (1 ≤ m → s (j0 + (m - 1)) = γ.len))
    (h1 : 0 ≤ sA 1) (h1k : sA 1 ≤ sA (kA - 1))
    (hkl : sA (kA - 1) ≤ (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len)
    (hnc : ¬ IsClosedCurve
      (curveRestrict (curveArc γ hcl t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) h1 h1k hkl)) :
    IsDeltaEpsN
      (curveRestrict (curveArc γ hcl t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) h1 h1k hkl)
      δ ε n := by sorry
