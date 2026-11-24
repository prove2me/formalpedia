-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_gamOf_comm
-- name    : Formalism.L2.SG.NormCut.gamOf_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:03.308827+00:00
-- url     : https://prove2.me/theorems/bca9b13d-f68c-4d37-8c65-b3e818da923a
-- title:
--   Norm Cut: gam Of comm
-- statement:
--   The Norm Cut construction uses the gam Of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]

theorem Formalism.L2.SG.NormCut.gamOf_comm (U : Set I) (p : I → ℂ) (x y : I) : gamOf U p (x * y) = gamOf U p (y * x) := by sorry
