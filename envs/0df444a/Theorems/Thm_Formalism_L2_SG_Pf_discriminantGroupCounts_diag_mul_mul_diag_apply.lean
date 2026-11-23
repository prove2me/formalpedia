-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_diag_mul_mul_diag_apply
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.diag_mul_mul_diag_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:29.11389+00:00
-- url     : https://prove2.me/theorems/2282eaa5-7600-4771-8796-06697343f2c7
-- title:
--   discriminant Group Counts: diag mul mul diag apply
-- statement:
--   The discriminant Group Counts construction uses the diag mul mul diag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L13-L15

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.diag_mul_mul_diag_apply (d : m → A) (T : Matrix m m A) (i j : m) :
    (diagonal d * T * diagonal d) i j = d i * T i j * d j := by sorry
