-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_valS
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_valS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:14.865622+00:00
-- url     : https://prove2.me/theorems/e9b4ff1a-3b1b-4e5e-a1c5-ce9e9d283094
-- title:
--   G1: flt op val S
-- statement:
--   The G1 construction uses the flt op val S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L303-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L303-L323

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_valS {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) := by sorry
