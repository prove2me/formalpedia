-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_lieGram_eq
-- name    : Formalism.L2.LamCM.lieGram_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:28.65014+00:00
-- url     : https://prove2.me/theorems/c69cd839-de4d-5262-b8c7-eacecb2d7978
-- title:
--   Lam CM: lie Gram eq
-- statement:
--   The Lam CM construction uses the lie Gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L116-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L116-L124

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

theorem Formalism.L2.LamCM.lieGram_eq {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    lieGram Hm W = (Real.pi : ℂ) • (W * Hm * W.conjTranspose).transpose := by sorry
