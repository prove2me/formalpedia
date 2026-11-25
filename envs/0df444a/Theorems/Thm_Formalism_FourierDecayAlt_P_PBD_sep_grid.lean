-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_sep_grid
-- name    : Formalism.FourierDecayAlt.P.PBD.sep_grid
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:27.614008+00:00
-- url     : https://prove2.me/theorems/16bdc3d1-2a0a-4cdb-82da-8722570f0bf0
-- title:
--   PBD: sep grid
-- statement:
--   The PBD construction uses the sep grid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L115-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean#L115-L139

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

theorem Formalism.FourierDecayAlt.P.PBD.sep_grid (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) {b b' : ℕ} {y y' : ℝ}
    (hy : y ∈ S.grid v b) (hy' : y' ∈ S.grid v b') (hne : b ≠ b') {e e' : ℝ}
    (he : e ∈ ({0, 1} : Finset ℝ)) (he' : e' ∈ ({0, 1} : Finset ℝ)) :
    (S.Ntop : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')| := by sorry
