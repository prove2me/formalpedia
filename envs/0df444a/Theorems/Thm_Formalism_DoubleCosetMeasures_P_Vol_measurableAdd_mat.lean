-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measurableAdd_mat
-- name    : Formalism.DoubleCosetMeasures.P.Vol.measurableAdd_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:14.310349+00:00
-- url     : https://prove2.me/theorems/e74b92d3-1aec-4147-b98a-e609337f890c
-- title:
--   Vol: measurable Add mat
-- statement:
--   The Vol construction uses the measurable Add mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L179-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L179-L183

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

theorem Formalism.DoubleCosetMeasures.P.Vol.measurableAdd_mat (n a : ℕ) : MeasurableAdd (Matrix (Fin n) (Fin a) F) := by sorry
