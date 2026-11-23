-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_exists_continuous_lowerUpper_entry
-- name    : Formalism.DoubleCosetMeasures.P.Supp.exists_continuous_lowerUpper_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:21.265918+00:00
-- url     : https://prove2.me/theorems/348d8b80-efc1-4265-b865-5d4c99e34842
-- title:
--   Supp: exists continuous lower Upper entry
-- statement:
--   The Supp construction uses the exists continuous lower Upper entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L42-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L42-L82

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
variable [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.DoubleCosetMeasures.P.Supp.exists_continuous_lowerUpper_entry (m : ℕ) : ∃ E : Fin n → Fin n → Matrix (Fin n) (Fin n) K → K,
    (∀ i j, Continuous (E i j)) ∧ ∀ i j, (min i j).val < m → ∀ h u : Matrix (Fin n) (Fin n) K,
      IsLowUni h → IsUpUni u → E i j (h * u) = (h + u - 1) i j := by sorry
