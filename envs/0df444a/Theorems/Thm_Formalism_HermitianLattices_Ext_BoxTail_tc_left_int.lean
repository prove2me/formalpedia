-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_left_int
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_left_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:52.782613+00:00
-- url     : https://prove2.me/theorems/1ea9cef1-09ff-4d8b-8231-6995d28d38d9
-- title:
--   Box Tail: tc left int
-- statement:
--   The Box Tail construction uses the tc left int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L157-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L157-L244

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_left_int {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z η σ T M : ℝ)
    (hz : 0 < z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T)
    (hL : ∀ u : ℝ, |u| ≤ T → DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0)
    (hM : ∀ u : ℝ, |u| ≤ T → ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (4 * Real.log (1 + 800 * T)) := by sorry
