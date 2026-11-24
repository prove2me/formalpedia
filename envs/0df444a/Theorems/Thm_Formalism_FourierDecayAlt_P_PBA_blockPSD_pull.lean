-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_pull
-- name    : Formalism.FourierDecayAlt.P.PBA.blockPSD_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:10.440803+00:00
-- url     : https://prove2.me/theorems/c8b2f8f4-4c3b-4650-92be-732bf097dd2c
-- title:
--   PBA: block PSD pull
-- statement:
--   The PBA construction uses the block PSD pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L20-L36

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

theorem Formalism.FourierDecayAlt.P.PBA.blockPSD_pull {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X)
    (f g : X → Z) (hf : ∀ h ∈ Y, f h ∈ P) (hg : ∀ h ∈ Y, g h ∈ P) :
    KB.BlockPSD Y Y (fun h h' => H (f h) (f h')) (fun h h' => H (f h) (g h')) (fun h h' => H (g h) (g h')) := by sorry
