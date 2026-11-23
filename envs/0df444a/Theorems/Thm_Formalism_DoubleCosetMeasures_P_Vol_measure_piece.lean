-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_piece
-- name    : Formalism.DoubleCosetMeasures.P.Vol.measure_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:24.725372+00:00
-- url     : https://prove2.me/theorems/e4536806-1cef-4bae-8fd4-e26573c44181
-- title:
--   Vol: measure piece
-- statement:
--   The Vol construction uses the measure piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L189-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L189-L194

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

theorem Formalism.DoubleCosetMeasures.P.Vol.measure_piece {n a : ℕ} (ν : Measure (Matrix (Fin n) (Fin a) F)) [ν.IsAddLeftInvariant]
    (O : Subring F) (ϖ : F) (r : Matrix (Fin n) (Fin a) F) :
    ν (piece O ϖ r) = ν (IIset O ϖ) := by sorry
