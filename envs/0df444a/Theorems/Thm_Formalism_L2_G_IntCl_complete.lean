-- Prove2me | Theorems.Thm_Formalism_L2_G_IntCl_complete
-- name    : Formalism.L2.G.IntCl.complete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:16.54085+00:00
-- url     : https://prove2.me/theorems/8d13a199-9c5b-4c5f-b8b2-6a0efee05230
-- title:
--   Int Cl: complete
-- statement:
--   The Int Cl construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L230-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L230-L245

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.IntCl
open IsLocalRing
variable (A K L : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
  [IsScalarTower A K L]
include K

theorem Formalism.L2.G.IntCl.complete (hC : IsAdicComplete (maximalIdeal A) A) :
    haveI := isDVR A K L hC
    IsAdicComplete (maximalIdeal (integralClosure A L)) (integralClosure A L) := by sorry
