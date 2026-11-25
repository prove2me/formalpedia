-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_nodeOf_mem_grid_or_grid1
-- name    : Formalism.FourierDecayAlt.P.PBD.nodeOf_mem_grid_or_grid1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:05:32.888479+00:00
-- url     : https://prove2.me/theorems/935488f1-f9cf-4cd6-a734-0734077219ae
-- title:
--   PBD: node Of mem grid or grid1
-- statement:
--   The PBD construction uses the node Of mem grid or grid1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L145-L150

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

theorem Formalism.FourierDecayAlt.P.PBD.nodeOf_mem_grid_or_grid1 (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (ha : AdmList S v a) (z : C.Letter)
    (hz : z ∈ a) : (∃ n, n ≤ a.length ∧ nodeOf z ∈ S.grid v n) ∨ nodeOf z ∈ S.grid1 v := by sorry
