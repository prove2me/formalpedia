-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mul
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:44.906358+00:00
-- url     : https://prove2.me/theorems/8088caae-cb39-40ca-a2e4-dd7137cf5af0
-- title:
--   G1: flt twist Mat mul
-- statement:
--   The G1 construction uses the flt twist Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/AlmostEverywhereSpherical.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/AlmostEverywhereSpherical.lean#L105-L118

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by sorry
