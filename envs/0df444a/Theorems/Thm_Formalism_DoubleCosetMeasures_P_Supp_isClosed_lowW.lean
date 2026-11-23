-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_lowW
-- name    : Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:14.491949+00:00
-- url     : https://prove2.me/theorems/6eb600b6-8101-43e6-9944-47c43443cfa9
-- title:
--   Supp: is Closed low W
-- statement:
--   The Supp construction uses the is Closed low W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L224-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L224-L235

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

theorem Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowW {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (s : List ℕ) (t : ℕ → Kˣ) (wi : Matrix (Fin s.sum) (Fin s.sum) K)
    (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1) :
    IsClosed (lowW K s t : Set (GL (Fin s.sum) K)) := by sorry
