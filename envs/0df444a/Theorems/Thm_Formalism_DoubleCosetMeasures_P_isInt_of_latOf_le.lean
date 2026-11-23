-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_of_latOf_le
-- name    : Formalism.DoubleCosetMeasures.P.isInt_of_latOf_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:17.558844+00:00
-- url     : https://prove2.me/theorems/37313014-d313-434c-bd10-13b2ca616214
-- title:
--   P: is Int of lat Of le
-- statement:
--   The P construction uses the is Int of lat Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L145-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L145-L165

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
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
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.isInt_of_latOf_le (g h : GL (Fin n) K) (hle : latOf R h ≤ latOf R g) :
    IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by sorry
