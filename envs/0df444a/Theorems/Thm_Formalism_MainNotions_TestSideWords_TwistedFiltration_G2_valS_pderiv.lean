-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_valS_pderiv
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:41.14328+00:00
-- url     : https://prove2.me/theorems/ae14bba4-c701-41bc-ac4a-39250d94e4ce
-- title:
--   G2: val S pderiv
-- statement:
--   The G2 construction uses the val S pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/MaxTwistDegreePderivLeAddOne.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/MaxTwistDegreePderivLeAddOne.lean#L136-L141

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_pderiv (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (pderiv v F) + ((1 : ℤ) : WithTop ℤ) := by sorry
