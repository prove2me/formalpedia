-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_IsUTm_mul
-- name    : Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:22.443428+00:00
-- url     : https://prove2.me/theorems/c7b275f4-47f3-4857-a2b5-f387a1e5ef42
-- title:
--   Is UTm: mul
-- statement:
--   The Is UTm construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L21-L37

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

theorem Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by sorry
