-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_lu_rec
-- name    : Formalism.DoubleCosetMeasures.P.Supp.lu_rec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:40.738969+00:00
-- url     : https://prove2.me/theorems/644fd13b-18d6-4447-bd36-5ce5004ed332
-- title:
--   Supp: lu rec
-- statement:
--   The Supp construction uses the lu rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L84-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L84-L114

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

theorem Formalism.DoubleCosetMeasures.P.Supp.lu_rec : ∃ Ph Pu : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K,
    Continuous Ph ∧ Continuous Pu ∧
      ∀ h u, IsLowUni h → IsUpUni u → Ph (h * u) = h ∧ Pu (h * u) = u := by sorry
