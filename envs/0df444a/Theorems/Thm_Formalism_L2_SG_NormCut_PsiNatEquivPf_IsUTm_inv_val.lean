-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_IsUTm_inv_val
-- name    : Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.inv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:45.126492+00:00
-- url     : https://prove2.me/theorems/58f782c1-f8e7-4ed1-9e0d-662280d61607
-- title:
--   Is UTm: inv val
-- statement:
--   The Is UTm construction uses the inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L73-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L73-L94

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut Formalism.L2.SG.NormCut.PsiNatEquivPf
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.inv_val (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by sorry
