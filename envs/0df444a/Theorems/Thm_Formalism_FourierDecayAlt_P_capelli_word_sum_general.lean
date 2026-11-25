-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_word_sum_general
-- name    : Formalism.FourierDecayAlt.P.capelli_word_sum_general
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:05.928823+00:00
-- url     : https://prove2.me/theorems/b6d01080-9a08-4a76-ac57-88a51a7b7c29
-- title:
--   P: capelli word sum general
-- statement:
--   The P construction uses the capelli word sum general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L263-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L263-L269

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem Formalism.FourierDecayAlt.P.capelli_word_sum_general (k r : ℕ) (Y : ℂ) : ∃ L : List (ℂ × List (Formalism.FourierDecayAlt.B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (Formalism.FourierDecayAlt.B.Mat k r))
      (f : Formalism.FourierDecayAlt.B.Mat k r → E),
      Formalism.FourierDecayAlt.B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ Formalism.FourierDecayAlt.B.GV k r →
        Formalism.FourierDecayAlt.Q.CV k r Y f g = (L.map fun cw => cw.1 • Formalism.FourierDecayAlt.B.Rw cw.2 f g).sum := by sorry
