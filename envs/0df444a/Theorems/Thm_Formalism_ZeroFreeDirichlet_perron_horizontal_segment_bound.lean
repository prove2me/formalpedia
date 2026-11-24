-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_horizontal_segment_bound
-- name    : Formalism.ZeroFreeDirichlet.perron_horizontal_segment_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:02.099584+00:00
-- url     : https://prove2.me/theorems/4ffae4d9-5fc9-4c6d-9300-6ab7470f8d54
-- title:
--   Zero Free Dirichlet: perron horizontal segment bound
-- statement:
--   The Zero Free Dirichlet construction uses the perron horizontal segment bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L71-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L71-L121

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

theorem Formalism.ZeroFreeDirichlet.perron_horizontal_segment_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T x v σ₀ σ₁ : ℝ) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁)
    (hx1 : σ₁ ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by sorry
