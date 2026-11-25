-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_locProb_push
-- name    : Formalism.FourierDecayAlt.P.PBD.locProb_push
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:57:33.647686+00:00
-- url     : https://prove2.me/theorems/d46ad83f-6ded-4938-8063-fd0635bd3bd4
-- title:
--   PBD: loc Prob push
-- statement:
--   The PBD construction uses the loc Prob push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L271-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L271-L291

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

theorem Formalism.FourierDecayAlt.P.PBD.locProb_push (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (n' : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (mk : List ℝ → List C.Letter)
    (hmk : ∀ j : Fin K → Fin (d + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (j b))) ∧
      (mk (List.ofFn fun b => grid b (j b))).length ≤ n') :
    KB.LocProb S v n' (pushU grid mk) (pushTh grid mk) := by sorry
