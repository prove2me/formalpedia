-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_g_pascal
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_g_pascal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:39.28587+00:00
-- url     : https://prove2.me/theorems/bea0b60c-e4ac-4f15-a8bf-b2323ec5926f
-- title:
--   G1: flt g pascal
-- statement:
--   The G1 construction uses the flt g pascal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L18-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L18-L88

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
open Classical

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_g_pascal (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) (a : σ) :
    flt_g R (m + Finsupp.single a 1) be =
      flt_g R m be * X a + (if a ∈ be.support then flt_g R m (be - Finsupp.single a 1) else 0) := by sorry
