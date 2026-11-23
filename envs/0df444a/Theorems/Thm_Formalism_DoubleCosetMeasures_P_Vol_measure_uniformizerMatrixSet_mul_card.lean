-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_uniformizerMatrixSet_mul_card
-- name    : Formalism.DoubleCosetMeasures.P.Vol.measure_uniformizerMatrixSet_mul_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:04.876327+00:00
-- url     : https://prove2.me/theorems/5e299481-fb39-4deb-97f5-982403245e94
-- title:
--   Vol: measure uniformizer Matrix Set mul card
-- statement:
--   The Vol construction uses the measure uniformizer Matrix Set mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L235-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L235-L247

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

theorem Formalism.DoubleCosetMeasures.P.Vol.measure_uniformizerMatrixSet_mul_card (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    [Finite (kF O ϖ hϖ)] (n a : ℕ) (ν : Measure (Matrix (Fin n) (Fin a) F))
    [ν.IsAddLeftInvariant] :
    ν (IIset O ϖ) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (n * a) = ν (intMat O n a) := by sorry
