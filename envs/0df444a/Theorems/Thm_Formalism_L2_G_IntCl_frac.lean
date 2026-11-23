-- Prove2me | Theorems.Thm_Formalism_L2_G_IntCl_frac
-- name    : Formalism.L2.G.IntCl.frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:01.716186+00:00
-- url     : https://prove2.me/theorems/9f2679fd-54a8-443f-8ca1-50b21f2699cb
-- title:
--   Int Cl: frac
-- statement:
--   The Int Cl construction uses the frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L190-L191

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

theorem Formalism.L2.G.IntCl.frac : IsFractionRing (integralClosure A L) L := by sorry
