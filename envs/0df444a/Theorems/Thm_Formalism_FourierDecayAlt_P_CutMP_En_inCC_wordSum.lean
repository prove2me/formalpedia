-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_inCC_wordSum
-- name    : Formalism.FourierDecayAlt.P.CutMP.En.inCC_wordSum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:24.828457+00:00
-- url     : https://prove2.me/theorems/013d4776-84af-4d1c-9ef5-91e89508870a
-- title:
--   En: in CC word Sum
-- statement:
--   The En construction uses the in CC word Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnCVInCC.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnCVInCC.lean#L12-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVInCC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En

theorem Formalism.FourierDecayAlt.P.CutMP.En.inCC_wordSum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum)
  := by sorry
