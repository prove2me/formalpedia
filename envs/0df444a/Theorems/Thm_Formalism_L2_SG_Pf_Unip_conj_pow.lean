-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_pow
-- name    : Formalism.L2.SG.Pf.Unip.conj_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:28.898807+00:00
-- url     : https://prove2.me/theorems/cd52cfe6-f112-4d4a-bc59-d8d3f8769e5d
-- title:
--   Unip: conj pow
-- statement:
--   The Unip construction uses the conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L15-L22

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

theorem Formalism.L2.SG.Pf.Unip.conj_pow {G G' Z : Matrix ι ι K} (h : G * G' = 1) (j : ℕ) : G' * Z ^ j * G = (G' * Z * G) ^ j := by sorry
