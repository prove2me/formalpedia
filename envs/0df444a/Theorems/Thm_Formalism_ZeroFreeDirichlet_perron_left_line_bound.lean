-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_left_line_bound
-- name    : Formalism.ZeroFreeDirichlet.perron_left_line_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:25.089601+00:00
-- url     : https://prove2.me/theorems/ce2b62e1-fc30-42c3-91c9-d3c3732dbb85
-- title:
--   Zero Free Dirichlet: perron left line bound
-- statement:
--   The Zero Free Dirichlet construction uses the perron left line bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L123-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L123-L191

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.perron_left_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (hc₁ : 0 ≤ c₁) (hC : 0 ≤ C) (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T u σ₁ δ ε : ℝ) (hy : 0 < y) (hu : |u| ≤ T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁) (hhalf : 1 / 2 ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) (hδ : 0 < δ) (hδB : ∀ β ∈ B, δ ≤ |σ₁ - β|) :
    ‖Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) := by sorry
