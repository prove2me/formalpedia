-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_diff2
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:23:21.055893+00:00
-- url     : https://prove2.me/theorems/7b8f597b-046a-57d4-9682-6103165e8afb
-- title:
--   Hyp: c T diff2
-- statement:
--   The Hyp construction uses the c T diff2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L103-L107

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff2 (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by sorry
