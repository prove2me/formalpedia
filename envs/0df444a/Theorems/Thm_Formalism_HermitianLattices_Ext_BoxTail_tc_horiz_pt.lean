-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_horiz_pt
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_horiz_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:06.391853+00:00
-- url     : https://prove2.me/theorems/1595566f-7f8f-4ad3-a104-c3bd443b4aff
-- title:
--   Box Tail: tc horiz pt
-- statement:
--   The Box Tail construction uses the tc horiz pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L131-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L131-L155

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_horiz_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M y T x v : ℝ) (hy : 1 ≤ y)
    (hT : 0 < T) (hv : |v| = T) (hx2 : x ≤ 2)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((x : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ M * y ^ 2 / T ^ 2 := by sorry
