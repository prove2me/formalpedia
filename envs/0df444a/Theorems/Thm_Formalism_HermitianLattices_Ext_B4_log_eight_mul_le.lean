-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_B4_log_eight_mul_le
-- name    : Formalism.HermitianLattices.Ext.B4.log_eight_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:44.441993+00:00
-- url     : https://prove2.me/theorems/be0716cf-ab7c-45c4-bc14-5cd239e4db92
-- title:
--   B4: log eight mul le
-- statement:
--   The B4 construction uses the log eight mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/LogEightBound/ProgTwo.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/LogEightBound/ProgTwo.lean#L7-L15

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

theorem Formalism.HermitianLattices.Ext.B4.log_eight_mul_le {M : ℕ} (hM : 3 ≤ M) : Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ≤ 3 * Real.log M := by sorry
