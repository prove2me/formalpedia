-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_mem_val
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:46.177734+00:00
-- url     : https://prove2.me/theorems/7e79b20a-7943-432e-b01f-fab4b90e71d2
-- title:
--   G1: flt op mem val
-- statement:
--   The G1 construction uses the flt op mem val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L279-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L279-L289

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem_val {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    {F : MvPolynomial (ι × Fin n) R} {t : ℤ} (ht : (t : WithTop ℤ) ≤ valS LL S F) (al be : ι × Fin n →₀ ℕ)
    (N : ℕ) (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    twistSub LL S (lastIdx n) (monomial al 1 * divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) 1).F (t - N) := by sorry
