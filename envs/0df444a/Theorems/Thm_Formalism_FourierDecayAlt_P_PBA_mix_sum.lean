-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mix_sum
-- name    : Formalism.FourierDecayAlt.P.PBA.mix_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:09.359963+00:00
-- url     : https://prove2.me/theorems/993e46da-97c6-46bc-bbcd-81f7e2039a29
-- title:
--   PBA: mix sum
-- statement:
--   The PBA construction uses the mix sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L40-L49

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
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

theorem Formalism.FourierDecayAlt.P.PBA.mix_sum {X W : Type} (Y : Finset X) (Ws : Finset W) (κ : X → X → ℂ) (c : ℂ) (p : W → ℂ)
    (G : W → X → X → ℂ) :
    ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (c * ∑ w ∈ Ws, p w * G w h h') =
      c * ∑ w ∈ Ws, p w * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G w h h' := by sorry
