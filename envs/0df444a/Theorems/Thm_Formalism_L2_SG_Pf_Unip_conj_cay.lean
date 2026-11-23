-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_cay
-- name    : Formalism.L2.SG.Pf.Unip.conj_cay
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:46.162801+00:00
-- url     : https://prove2.me/theorems/9d8eac22-ead8-4d49-80fe-bdd368e7799c
-- title:
--   Unip: conj cay
-- statement:
--   The Unip construction uses the conj cay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L29-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]

theorem Formalism.L2.SG.Pf.Unip.conj_cay [Invertible (2 : K)] {G G' Z : Matrix ι ι K} (h : G * G' = 1) (N : ℕ) :
    G' * cay N Z * G = cay N (G' * Z * G) := by sorry
