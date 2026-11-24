-- Prove2me | Theorems.Thm_Formalism_L2_G_IntCl_complete_of_pow
-- name    : Formalism.L2.G.IntCl.complete_of_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:28.356321+00:00
-- url     : https://prove2.me/theorems/137412d5-49a0-4dc7-a31d-8e6ca5dba39d
-- title:
--   Int Cl: complete of pow
-- statement:
--   The Int Cl construction uses the complete of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/IsLocalRingOfComplete.lean#L32-L48

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

theorem Formalism.L2.G.IntCl.complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by sorry
