-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coeff_mem_of_ZP
-- name    : Formalism.L2.FormalSeriesBounds.RF.coeff_mem_of_ZP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:05.372917+00:00
-- url     : https://prove2.me/theorems/7b738e1d-3530-46a7-b748-158863de5c42
-- title:
--   RF: coeff mem of ZP
-- statement:
--   The RF construction uses the coeff mem of ZP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L26-L30

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.coeff_mem_of_ZP {σ : Type} {P : MvPolynomial σ C} (h : P ∈ ZP C σ) (O : Subring C) (m : σ →₀ ℕ) :
    P.coeff m ∈ O := by sorry
