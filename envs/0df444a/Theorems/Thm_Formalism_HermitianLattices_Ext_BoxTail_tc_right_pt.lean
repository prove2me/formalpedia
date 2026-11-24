-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_right_pt
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_right_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:08.022946+00:00
-- url     : https://prove2.me/theorems/877da34a-758c-4950-9657-e302c43bda9c
-- title:
--   Box Tail: tc right pt
-- statement:
--   The Box Tail construction uses the tc right pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L101-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L101-L129

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_right_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y t : ℝ) (hy : 0 < y) (ht : t ≠ 0) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (1 + C₀) * y ^ 2 / t ^ 2 := by sorry
