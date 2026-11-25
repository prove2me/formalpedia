-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_numHC_addI_le
-- name    : Formalism.FourierDecayAlt.P.CutBP.JmuHC.numHC_addI_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:20.799129+00:00
-- url     : https://prove2.me/theorems/11a9950b-fa04-403c-97a2-47548c457e88
-- title:
--   Jmu HC: num HC add I le
-- statement:
--   The Jmu HC construction uses the num HC add I le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L133-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L133-L211

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}

theorem Formalism.FourierDecayAlt.P.CutBP.JmuHC.numHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    numHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * numHC x := by sorry
