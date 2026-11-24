-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_real_zero_residue_term_bound
-- name    : Formalism.ZeroFreeDirichlet.real_zero_residue_term_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:59.128795+00:00
-- url     : https://prove2.me/theorems/d404a3b3-6dbc-4620-95e6-c4298c9629d2
-- title:
--   Zero Free Dirichlet: real zero residue term bound
-- statement:
--   The Zero Free Dirichlet construction uses the real zero residue term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L193-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L193-L214

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

theorem Formalism.ZeroFreeDirichlet.real_zero_residue_term_bound (y β σ₁ ε : ℝ) (hy : 1 ≤ y) (hβ : 1 / 2 ≤ β) (hβσ : β ≤ σ₁) (hε : 0 < ε)
    (hgap : ε ≤ 1 - σ₁) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (2 / ε) := by sorry
