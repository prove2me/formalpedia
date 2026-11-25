-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_diff
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:23:15.076388+00:00
-- url     : https://prove2.me/theorems/748af82e-e8a7-54f4-8592-9ddde1876fdf
-- title:
--   Hyp: c T diff
-- statement:
--   The Hyp construction uses the c T diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L109-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L109-L157

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by sorry
