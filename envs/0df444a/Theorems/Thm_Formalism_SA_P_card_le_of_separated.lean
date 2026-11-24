-- Prove2me | Theorems.Thm_Formalism_SA_P_card_le_of_separated
-- name    : Formalism.SA.P.card_le_of_separated
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:37.066814+00:00
-- url     : https://prove2.me/theorems/2c41e77e-50b9-42d6-81f2-1d05be3b812a
-- title:
--   P: card le of separated
-- statement:
--   The P construction uses the card le of separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PackingCountGeometricMean.lean#L7-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PackingCountGeometricMean.lean#L7-L67

import Definitions.Def_Formalism_LatticeRigidity_PackCount
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PackingCountGeometricMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Module
open Formalism Formalism.SA Formalism.SA.P

theorem Formalism.SA.P.card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} (S : Finset α) (g : α → E) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖)
    (hbd : ∀ x ∈ S, ‖g x‖ ≤ R) :
    (S.card : ℝ) ≤ (1 + 2 * R / lam) ^ finrank ℝ E := by sorry
