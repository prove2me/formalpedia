-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_lu_entry
-- name    : Formalism.DoubleCosetMeasures.P.Supp.lu_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:24.072211+00:00
-- url     : https://prove2.me/theorems/01c985c3-71cc-4e26-9cde-f0dee3c96582
-- title:
--   Supp: lu entry
-- statement:
--   The Supp construction uses the lu entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L15-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L15-L38

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
variable {K : Type} [CommRing K] {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.Supp.lu_entry (h u : Matrix (Fin n) (Fin n) K) (hh : IsLowUni h) (hu : IsUpUni u)
    (i j : Fin n) :
    (h * u) i j = (∑ k, if k < i ∧ k < j then h i k * u k j else 0) + (h + u - 1) i j := by sorry
