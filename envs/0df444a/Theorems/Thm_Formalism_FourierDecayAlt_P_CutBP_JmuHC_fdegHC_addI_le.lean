-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_JmuHC_fdegHC_addI_le
-- name    : Formalism.FourierDecayAlt.P.CutBP.JmuHC.fdegHC_addI_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:25:07.848026+00:00
-- url     : https://prove2.me/theorems/65c90a09-295d-4cc3-b512-6ab3f3e3e8c4
-- title:
--   Jmu HC: fdeg HC add I le
-- statement:
--   The Jmu HC construction uses the fdeg HC add I le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L213-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean#L213-L223

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

theorem Formalism.FourierDecayAlt.P.CutBP.JmuHC.fdegHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    PI.UpqRep.fdegHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * PI.UpqRep.fdegHC x := by sorry
