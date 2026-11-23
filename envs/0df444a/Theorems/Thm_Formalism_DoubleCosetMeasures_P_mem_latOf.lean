-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_latOf
-- name    : Formalism.DoubleCosetMeasures.P.mem_latOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:49.453595+00:00
-- url     : https://prove2.me/theorems/8b7e9be0-9634-4e37-84bc-9d34d36657ae
-- title:
--   P: mem lat Of
-- statement:
--   The P construction uses the mem lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsIntOfLatOfLe.lean#L123-L127

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.mem_latOf (g : GL (Fin n) K) (w : Fin n → K) :
    w ∈ latOf R g ↔ ∃ v : Fin n → R, (g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (v j : K)) = w := by sorry
