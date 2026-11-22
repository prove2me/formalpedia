-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_mem_lowW_iff
-- name    : Formalism.DoubleCosetMeasures.P.Supp.mem_lowW_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:07.969509+00:00
-- url     : https://prove2.me/theorems/84b85429-5323-4794-b456-6f27fb5c5818
-- title:
--   Supp: mem low W iff
-- statement:
--   The Supp construction uses the mem low W iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L207-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L207-L222

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

theorem Formalism.DoubleCosetMeasures.P.Supp.mem_lowW_iff {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ)
    (wi : Matrix (Fin s.sum) (Fin s.sum) K) (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1)
    (g : GL (Fin s.sum) K) :
    g ∈ lowW K s t ↔ IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧
      IsLowUni (wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) := by sorry
