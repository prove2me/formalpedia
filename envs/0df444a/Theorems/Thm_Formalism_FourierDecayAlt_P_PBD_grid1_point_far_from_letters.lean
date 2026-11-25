-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_grid1_point_far_from_letters
-- name    : Formalism.FourierDecayAlt.P.PBD.grid1_point_far_from_letters
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:43:23.974147+00:00
-- url     : https://prove2.me/theorems/b2f6ae87-f84c-5bb7-bff5-62ad9979ddac
-- title:
--   PBD: grid1 point far from letters
-- statement:
--   The PBD construction uses the grid1 point far from letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L169-L181

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

theorem Formalism.FourierDecayAlt.P.PBD.grid1_point_far_from_letters (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {y : ℝ} (hy : y ∈ S.grid1 v) (hyn : y ∉ a.map nodeOf) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by sorry
