-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_card_ne_zero_of_bij
-- name    : Formalism.L2.SG.NormCut.card_ne_zero_of_bij
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:51.158132+00:00
-- url     : https://prove2.me/theorems/d0e53060-c64d-4930-bb46-d50cfde9f3c3
-- title:
--   Norm Cut: card ne zero of bij
-- statement:
--   The Norm Cut construction uses the card ne zero of bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L174-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L174-L180

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
variable {I : Type} [Group I] [Fintype I]

theorem Formalism.L2.SG.NormCut.card_ne_zero_of_bij {C : Type*} (A U : Set I) (s : C → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I))) :
    (Nat.card A : ℂ) ≠ 0 ∧ (Nat.card U : ℂ) ≠ 0 := by sorry
