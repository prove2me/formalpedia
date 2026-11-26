-- Prove2me | Theorems.Thm_ArcShortWindowEdgeCount
-- name    : ArcShortWindowEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:04.857129+00:00
-- url     : https://prove2.me/theorems/20ae42cf-4766-46df-86c2-37fa0e0c4d73
-- title:
--   Arc Short Window Edge Count: Arc Short Window Edge Count
-- statement:
--   If the circular arc `γ|_{[t,t']}` (`curveArc`) has a named geodesic resolution `(kA,sA)`
--   whose interior window, between its own breakpoints `sA 1` and `sA (kA-1)`, has length at most
--   `δ`, then `kA ≤ n + 3`. This is the counting fact `CutTypeI`'s short-window branch needs: unlike
--   `ArcDeltaEpsNCount` (which bounds the *content* of that window's own resolution, existentially),
--   this bounds `kA` itself, the number of edges of the *given* resolution `sA` — a short window does
--   not bound this in general (a cluster of arbitrarily many edges each shorter than `δ` can still fit
--   in a window of length at most `δ`), so the bound goes via `γ`'s own `(δ,ε,n)`-curve counting
--   clauses applied at the pulled-back window, plus a direct "at most one long edge" fact about `sA`'s
--   own monotonicity that needs no correspondence with `γ` at all.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcShortWindowEdgeCount.lean#L19-L192
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcShortWindowEdgeCount.lean#L19-L192

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_ShortWindowAtMostOneLongEdge
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_ArcShortWindowEdgeCount
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_ShortWindowAtMostOneLongEdge
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set

theorem ArcShortWindowEdgeCount {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
    (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1)
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
    (hshort : sA (kA - 1) - sA 1 ≤ δ) :
    kA ≤ n + 3 := by sorry
