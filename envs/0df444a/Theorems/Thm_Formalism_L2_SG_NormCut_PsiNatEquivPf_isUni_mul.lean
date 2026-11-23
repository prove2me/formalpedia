-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_isUni_mul
-- name    : Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:48.592255+00:00
-- url     : https://prove2.me/theorems/66419b27-eab4-4ccf-adda-11e78ab7d212
-- title:
--   Psi Nat Equiv Pf: is Uni mul
-- statement:
--   The Psi Nat Equiv Pf construction uses the is Uni mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCorePsiNatEquiv.lean#L96-L100

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

theorem Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by sorry
