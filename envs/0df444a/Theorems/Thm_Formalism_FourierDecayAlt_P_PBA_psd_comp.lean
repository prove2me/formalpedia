-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_comp
-- name    : Formalism.FourierDecayAlt.P.PBA.psd_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:48.845302+00:00
-- url     : https://prove2.me/theorems/b482a111-45f4-4c8f-851c-ab8d2dca1297
-- title:
--   PBA: psd comp
-- statement:
--   The PBA construction uses the psd comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L15-L18

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section

theorem Formalism.FourierDecayAlt.P.PBA.psd_comp {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) : TB.PSDOn Y (fun x y => H (g x) (g y)) := by sorry
