-- Prove2me | Theorems.Thm_ArcGeodesicResolution
-- name    : ArcGeodesicResolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:53.375517+00:00
-- url     : https://prove2.me/theorems/4cf4ddc3-8b38-5be8-81fc-d4d6581bed74
-- title:
--   Arc Geodesic Resolution: Arc Geodesic Resolution
-- statement:
--   Given a geodesic resolution `(k,s)` of a closed curve `γ` and arbitrary `t,t' ∈ [0,γ.len]`,
--   the circular arc `γ|_{[t,t']}` (`curveArc`) admits a named geodesic resolution `(kA,sA)` in which
--   the up-to-two truncated end edges (`[sA 0, sA 1]` and `[sA (kA-1), sA kA]`) are placed as the
--   first and last edges, and every other breakpoint of `sA` (indices `1,…,kA-1`) is a genuine
--   breakpoint of `s`, shifted into the arc's own parametrization: in the ordinary case `t ≤ t'`, all
--   of `sA`'s breakpoints at indices `1,…,kA-1` are `s`-breakpoints starting from a single index `j0`,
--   shifted by `-t`; in the wrap case `t' < t`, they split into a prefix (indices `1,…,m`, from the
--   tail `γ|_{[t,γ.len]}`) of `s`-breakpoints shifted by `-t`, followed by a suffix (indices
--   `m+1,…,kA-1`, from the head `γ|_{[0,t']}`) of `s`-breakpoints shifted by `γ.len - t`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcGeodesicResolution.lean#L18-L324
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcGeodesicResolution.lean#L18-L324

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictGeodesicResolutionTruncated
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_ArcGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_RestrictGeodesicResolutionTruncated

set_option autoImplicit false
open Set

theorem ArcGeodesicResolution {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (k : ℕ) (s : ℕ → ℝ) (hs : IsGeodesicResolution γ k s)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) :
    ∃ (kA : ℕ) (sA : ℕ → ℝ),
      1 ≤ kA ∧
      IsGeodesicResolution (curveArc γ hcl t t' ht0 htl ht'0 ht'l) kA sA ∧
      (t ≤ t' → ∃ j0 : ℕ,
        ∀ i : ℕ, 1 ≤ i → i ≤ kA - 1 → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
      (t' < t → ∃ j0 m : ℕ,
        (∀ i : ℕ, 1 ≤ i → i ≤ m → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
        (∀ i : ℕ, m < i → i ≤ kA - 1 → i - m ≤ k ∧
          sA i = (γ.len - t) + s (i - m)) ∧
        (1 ≤ m → s (j0 + (m - 1)) = γ.len)) := by sorry
