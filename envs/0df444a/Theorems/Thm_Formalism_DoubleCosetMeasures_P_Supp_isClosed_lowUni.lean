-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_lowUni
-- name    : Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:31.181201+00:00
-- url     : https://prove2.me/theorems/53dfce39-80a7-4c3b-8e80-5b093c807f83
-- title:
--   Supp: is Closed low Uni
-- statement:
--   The Supp construction uses the is Closed low Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L183-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L183-L192

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowUni : IsClosed {x : Matrix (Fin n) (Fin n) K | IsLowUni x} := by sorry
