-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_sum_pair
-- name    : Formalism.FourierDecayAlt.P.PBA.sum_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:05.579738+00:00
-- url     : https://prove2.me/theorems/94f83dc4-5baf-41e6-865c-be0211042f75
-- title:
--   PBA: sum pair
-- statement:
--   The PBA construction uses the sum pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SizeAtNonneg.lean#L23-L38

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

theorem Formalism.FourierDecayAlt.P.PBA.sum_pair {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by sorry
