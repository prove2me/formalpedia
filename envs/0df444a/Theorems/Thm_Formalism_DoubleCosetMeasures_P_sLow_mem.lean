-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_sLow_mem
-- name    : Formalism.DoubleCosetMeasures.P.sLow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:47.390958+00:00
-- url     : https://prove2.me/theorems/24f8c247-5c1f-4e7d-8029-ba0db94b4401
-- title:
--   P: s Low mem
-- statement:
--   The P construction uses the s Low mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L37-L43

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

theorem Formalism.DoubleCosetMeasures.P.sLow_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sLow x ∈ R := by sorry
