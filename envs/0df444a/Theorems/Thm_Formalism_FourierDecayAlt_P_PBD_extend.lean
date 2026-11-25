-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_extend
-- name    : Formalism.FourierDecayAlt.P.PBD.extend
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:56.379351+00:00
-- url     : https://prove2.me/theorems/3a58b262-dc6a-461d-8509-b7f2ed67eeb9
-- title:
--   PBD: extend
-- statement:
--   The PBD construction uses the extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L183-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L183-L238

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

theorem Formalism.FourierDecayAlt.P.PBD.extend (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (v : Fin S.f) (a : List C.Letter)
    (haA : D.AdmAt S v a) (ys : List ℝ) (H1 : ys.Pairwise fun y y' => 4 < |y - y'|)
    (H2 : ∀ y ∈ ys, ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2|)
    (H3 : ∀ i (hi : i < ys.length), ys[i] ∈ S.grid v (ys.length + a.length - i) ∪ S.grid1 v)
    (hlen : ys.length + a.length ≤ S.Ntop) :
    D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) := by sorry
