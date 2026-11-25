-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_B4_progTwo
-- name    : Formalism.HermitianLattices.Ext.B4.progTwo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:18.542298+00:00
-- url     : https://prove2.me/theorems/179738e3-8d67-4afe-8bfc-12b45ca2b745
-- title:
--   B4: prog Two
-- statement:
--   The B4 construction uses the prog Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/LogEightBound/ProgTwo.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/LogEightBound/ProgTwo.lean#L17-L38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_LogEightBound_ProgTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.B4

theorem Formalism.HermitianLattices.Ext.B4.progTwo : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∃ p p' : ℕ, p ≠ p' ∧ p.Prime ∧ p'.Prime ∧
    p ≡ 1 [MOD M] ∧ p' ≡ 1 [MOD M] ∧ Real.log p ≤ C * Real.log M ^ 2 ∧ Real.log p' ≤ C * Real.log M ^ 2 := by sorry
