-- Prove2me | Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_mem
-- name    : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:49.589819+00:00
-- url     : https://prove2.me/theorems/fce27e65-19b4-48a3-bd43-a9149305560f
-- title:
--   G1: flt op mem
-- statement:
--   The G1 construction uses the flt op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L253-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/SumCCMulSumOfMulEqOne.lean#L253-L263

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

theorem Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (al be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al 1 * divDer be F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F (t - (flt_cost LL S bm al + flt_cost LL S (!bm) be)) := by sorry
