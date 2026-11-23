-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_intMat_eq_iUnion
-- name    : Formalism.DoubleCosetMeasures.P.Vol.intMat_eq_iUnion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:23.24745+00:00
-- url     : https://prove2.me/theorems/437f9695-97d4-4022-982e-484d993e6abb
-- title:
--   Vol: int Mat eq i Union
-- statement:
--   The Vol construction uses the int Mat eq i Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L200-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L200-L215

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
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]

theorem Formalism.DoubleCosetMeasures.P.Vol.intMat_eq_iUnion (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (n a : ℕ) :
    intMat O n a = ⋃ c : Fin n → Fin a → kF O ϖ hϖ, piece O ϖ (repM O ϖ hϖ c) := by sorry
