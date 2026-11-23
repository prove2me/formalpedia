-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_latOf_le
-- name    : Formalism.DoubleCosetMeasures.P.latOf_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.041812+00:00
-- url     : https://prove2.me/theorems/90bb4c9e-062e-4260-a578-7b63827fb20c
-- title:
--   P: lat Of le
-- statement:
--   The P construction uses the lat Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L129-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L129-L143

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

theorem Formalism.DoubleCosetMeasures.P.latOf_le (g h : GL (Fin n) K)
    (hM : IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    latOf R h ≤ latOf R g := by sorry
