-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_Th_mem
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:34.92951+00:00
-- url     : https://prove2.me/theorems/a4a76f63-70a0-4a61-82fe-3771d015b960
-- title:
--   G1: flt Th mem
-- statement:
--   The G1 construction uses the flt Th mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L190-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L190-L239

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {P : MvPolynomial (ι × Fin n) (GLLaurent R n)}
    (hP : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) :
    flt_Th LL S j P ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by sorry
