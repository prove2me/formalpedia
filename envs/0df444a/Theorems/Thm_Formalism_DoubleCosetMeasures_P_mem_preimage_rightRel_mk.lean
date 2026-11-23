-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_preimage_rightRel_mk
-- name    : Formalism.DoubleCosetMeasures.P.mem_preimage_rightRel_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:56.970101+00:00
-- url     : https://prove2.me/theorems/915d8976-321c-439f-b641-29020216603f
-- title:
--   P: mem preimage right Rel mk
-- statement:
--   The P construction uses the mem preimage right Rel mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L11-L15

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
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
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P

theorem Formalism.DoubleCosetMeasures.P.mem_preimage_rightRel_mk {G : Type} [Group G] (K : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel K)) (x : G) :
    Quotient.mk (QuotientGroup.rightRel K) x = q ↔ x * q.out⁻¹ ∈ K := by sorry
