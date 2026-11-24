-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_norm_addChar
-- name    : Formalism.L2.SG.NormCut.PsiNatEquivPf.norm_addChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:51.82229+00:00
-- url     : https://prove2.me/theorems/fffe0765-8f1b-47cb-8161-eda9451aad92
-- title:
--   Psi Nat Equiv Pf: norm add Char
-- statement:
--   The Psi Nat Equiv Pf construction uses the norm add Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L113-L120

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

theorem Formalism.L2.SG.NormCut.PsiNatEquivPf.norm_addChar (ψ₀ : AddChar F ℂ) (a : F) : ‖ψ₀ a‖ = 1 := by sorry
