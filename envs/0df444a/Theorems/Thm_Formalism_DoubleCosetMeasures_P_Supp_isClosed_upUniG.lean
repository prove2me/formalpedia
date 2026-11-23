-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_upUniG
-- name    : Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUniG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:28.161146+00:00
-- url     : https://prove2.me/theorems/f6136245-4430-44ea-8404-ebafa0452ca4
-- title:
--   Supp: is Closed up Uni G
-- statement:
--   The Supp construction uses the is Closed up Uni G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L237-L243

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

theorem Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUniG {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (n : ℕ) : IsClosed (upUniG K n : Set (GL (Fin n) K)) := by sorry
