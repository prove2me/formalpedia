-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_upUni
-- name    : Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:31.696285+00:00
-- url     : https://prove2.me/theorems/bfeba848-5e69-44cf-8a57-6fd1c96c5372
-- title:
--   Supp: is Closed up Uni
-- statement:
--   The Supp construction uses the is Closed up Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L194-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L194-L203

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

theorem Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUni : IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by sorry
