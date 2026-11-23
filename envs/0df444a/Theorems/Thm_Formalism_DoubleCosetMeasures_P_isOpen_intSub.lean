-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_intSub
-- name    : Formalism.DoubleCosetMeasures.P.isOpen_intSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:27.472697+00:00
-- url     : https://prove2.me/theorems/0b95d288-70e8-4c3a-88e0-fdf948796917
-- title:
--   P: is Open int Sub
-- statement:
--   The P construction uses the is Open int Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L31-L33

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.DoubleCosetMeasures.P.isOpen_intSub (R : Subring K) (hR : IsOpen (R : Set K)) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : IsOpen (intSub R H : Set H) := by sorry
