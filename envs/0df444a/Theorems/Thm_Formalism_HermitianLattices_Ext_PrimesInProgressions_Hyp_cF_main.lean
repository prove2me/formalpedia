-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_main
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:00.736535+00:00
-- url     : https://prove2.me/theorems/65e4ae08-8af2-5c06-96c6-aded7ca5adda
-- title:
--   Hyp: c F main
-- statement:
--   The Hyp construction uses the c F main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperC.lean#L61-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperC.lean#L61-L133

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_main (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by sorry
