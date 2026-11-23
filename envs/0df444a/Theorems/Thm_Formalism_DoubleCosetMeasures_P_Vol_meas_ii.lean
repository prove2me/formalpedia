-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_ii
-- name    : Formalism.DoubleCosetMeasures.P.Vol.meas_ii
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:35.241346+00:00
-- url     : https://prove2.me/theorems/3267087a-b49e-4ffa-b898-33ca3a9a7b8e
-- title:
--   Vol: meas ii
-- statement:
--   The Vol construction uses the meas ii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L160-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L160-L171

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

theorem Formalism.DoubleCosetMeasures.P.Vol.meas_ii (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ0 : ϖ ≠ 0) (n a : ℕ) :
    MeasurableSet (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) := by sorry
