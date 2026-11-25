-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_lagCo_ne_zero
-- name    : Formalism.FourierDecayAlt.P.PBD.lagCo_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:10:43.834062+00:00
-- url     : https://prove2.me/theorems/2694949d-f7ad-471d-90f8-43e1426bfee2
-- title:
--   PBD: lag Co ne zero
-- statement:
--   The PBD construction uses the lag Co ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L248-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L248-L252

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.PBD.lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by sorry
