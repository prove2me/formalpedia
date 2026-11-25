-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_admissible_list_prepend
-- name    : Formalism.FourierDecayAlt.P.PBD.admissible_list_prepend
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:08:36.686861+00:00
-- url     : https://prove2.me/theorems/210d9b68-524e-44ab-b3c9-de40c65f3c7d
-- title:
--   PBD: admissible list prepend
-- statement:
--   The PBD construction uses the admissible list prepend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L101-L113

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

theorem Formalism.FourierDecayAlt.P.PBD.admissible_list_prepend (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (pre a : List C.Letter) (ha : AdmList S v a)
    (hpre : ∀ j (hj : j < pre.length), nodeOf (pre[j]'hj) ∈ S.grid v (pre.length + a.length - j) ∪ S.grid1 v)
    (hpp : pre.Pairwise Sep) (hpa : ∀ x ∈ pre, ∀ y ∈ a, Sep x y) : AdmList S v (pre ++ a) := by sorry
