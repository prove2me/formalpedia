-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_superdiag_mul
-- name    : Formalism.L2.SG.NormCut.PsiNatEquivPf.superdiag_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:52.904083+00:00
-- url     : https://prove2.me/theorems/0a6a5e8e-2a3d-48f7-b43c-5701f215b9be
-- title:
--   Psi Nat Equiv Pf: superdiag mul
-- statement:
--   The Psi Nat Equiv Pf construction uses the superdiag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L39-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L39-L71

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

theorem Formalism.L2.SG.NormCut.PsiNatEquivPf.superdiag_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by sorry
