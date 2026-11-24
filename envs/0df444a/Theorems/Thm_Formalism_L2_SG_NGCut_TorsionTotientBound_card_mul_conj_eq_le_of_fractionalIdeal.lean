-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_card_mul_conj_eq_le_of_fractionalIdeal
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:13.786805+00:00
-- url     : https://prove2.me/theorems/848531b0-beb2-49d7-b297-483b178217b2
-- title:
--   Torsion Totient Bound: card mul conj eq le of fractional Ideal
-- statement:
--   The Torsion Totient Bound construction uses the card mul conj eq le of fractional Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CardMulConjEqLeOfFractionalIdeal.lean#L10-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CardMulConjEqLeOfFractionalIdeal.lean#L10-L102

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CardMulConjEqLeOfFractionalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E) (hJ : J ≠ 0) (hm : m ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, x ∈ J ∧ x * IsCMField.complexConj E x = m) :
    (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
      2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by sorry
