-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_add
-- name    : Formalism.DoubleCosetMeasures.P.Vol.meas_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:39.78835+00:00
-- url     : https://prove2.me/theorems/0c0d3e29-7904-4f67-bdb8-675eb45cee3a
-- title:
--   Vol: meas add
-- statement:
--   The Vol construction uses the meas add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L173-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L173-L177

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

theorem Formalism.DoubleCosetMeasures.P.Vol.meas_add (n a : ℕ) (x : Matrix (Fin n) (Fin a) F) :
    Measurable (fun y : Matrix (Fin n) (Fin a) F => x + y) := by sorry
