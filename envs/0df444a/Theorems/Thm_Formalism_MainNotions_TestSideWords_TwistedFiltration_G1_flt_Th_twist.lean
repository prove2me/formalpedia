-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_Th_twist
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_twist
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:06.390582+00:00
-- url     : https://prove2.me/theorems/00818539-4bcc-4b56-9b36-dadf345745d0
-- title:
--   G1: flt Th twist
-- statement:
--   The G1 construction uses the flt Th twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L170-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L170-L188

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_twist {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    (MvPolynomial.map (twistSub (R := R) LL S j)).comp (flt_tay R (ι × Fin n)) =
      (flt_Th LL S j).comp (twistSub (R := R) LL S j) := by sorry
