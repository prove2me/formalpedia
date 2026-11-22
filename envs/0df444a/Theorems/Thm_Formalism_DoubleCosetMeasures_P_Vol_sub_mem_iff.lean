-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_sub_mem_iff
-- name    : Formalism.DoubleCosetMeasures.P.Vol.sub_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:06.178021+00:00
-- url     : https://prove2.me/theorems/67630a6c-4c26-4d57-a623-62207ffb44fb
-- title:
--   Vol: sub mem iff
-- statement:
--   The Vol construction uses the sub mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L36-L50

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]

theorem Formalism.DoubleCosetMeasures.P.Vol.sub_mem_iff {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {x y : F} (hx : x ∈ O) (hy : y ∈ O) :
    (∃ o ∈ O, x - y = ϖ * o) ↔
      (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨x, hx⟩ =
        Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) ⟨y, hy⟩) := by sorry
