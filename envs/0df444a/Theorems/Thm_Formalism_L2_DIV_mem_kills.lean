-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_kills
-- name    : Formalism.L2.DIV.mem_kills
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:57.510857+00:00
-- url     : https://prove2.me/theorems/d2e401c3-cf3c-4ff8-8092-47b3e2da273b
-- title:
--   DIV: mem kills
-- statement:
--   The DIV construction uses the mem kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/Tuples.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/Tuples.lean#L25-L26

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV

theorem Formalism.L2.DIV.mem_kills {G A : Type} [Group G] [CommGroup A] {H : Subgroup G} {ξ : G →* A} :
    ξ ∈ kills A H ↔ H ≤ ξ.ker := by sorry
