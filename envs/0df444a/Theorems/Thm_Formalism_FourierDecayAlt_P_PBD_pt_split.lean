-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pt_split
-- name    : Formalism.FourierDecayAlt.P.PBD.pt_split
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:10.276998+00:00
-- url     : https://prove2.me/theorems/1a9b5474-5103-49de-bbbf-44e91e77a3ca
-- title:
--   PBD: pt split
-- statement:
--   The PBD construction uses the pt split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L141-L143

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

theorem Formalism.FourierDecayAlt.P.PBD.pt_split (x : C.Letter) : x.2 = nodeOf x + (if x.1 then 0 else 1) ∧
    (if x.1 then (0 : ℝ) else 1) ∈ ({0, 1} : Finset ℝ) := by sorry
