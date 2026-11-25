-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pairwise_iff_idx
-- name    : Formalism.FourierDecayAlt.P.PBD.pairwise_iff_idx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:52.051177+00:00
-- url     : https://prove2.me/theorems/82225163-20fe-5e83-9b80-f90b6c95aea9
-- title:
--   PBD: pairwise iff idx
-- statement:
--   The PBD construction uses the pairwise iff idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L36-L45

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

theorem Formalism.FourierDecayAlt.P.PBD.pairwise_iff_idx (L : List C.Letter) :
    L.Pairwise Sep ↔ ∀ (j j' : ℕ) (hj : j < L.length) (hj' : j' < L.length), j ≠ j' → Sep (L[j]'hj) (L[j']'hj') := by sorry
