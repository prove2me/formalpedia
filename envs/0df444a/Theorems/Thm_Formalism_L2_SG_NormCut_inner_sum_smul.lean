-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_inner_sum_smul
-- name    : Formalism.L2.SG.NormCut.inner_sum_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:31.333242+00:00
-- url     : https://prove2.me/theorems/a299781b-d8a3-4172-9d5c-ed59fb6a2b06
-- title:
--   Norm Cut: inner sum smul
-- statement:
--   The Norm Cut construction uses the inner sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L86-L93

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

theorem Formalism.L2.SG.NormCut.inner_sum_smul {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (c : I → ℂ) (Z : I → K) :
    inner ℂ (∑ i, c i • Z i) (∑ j, c j • Z j) = ∑ i, ∑ j, conj (c i) * c j * inner ℂ (Z i) (Z j) := by sorry
