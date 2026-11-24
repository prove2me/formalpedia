-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_cont
-- name    : Formalism.HermitianLattices.Ext.BoxTail.tc_cont
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:58.210281+00:00
-- url     : https://prove2.me/theorems/2ed8baba-072e-4443-a1d0-2942f2b31853
-- title:
--   Box Tail: tc cont
-- statement:
--   The Box Tail construction uses the tc cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TailContourB.lean#L70-L99

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

theorem Formalism.HermitianLattices.Ext.BoxTail.tc_cont {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ u : ℝ) (hy : 0 < y)
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hL : DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0) :
    ContinuousAt (fun v : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((σ : ℂ) + (v : ℂ) * I)) u := by sorry
