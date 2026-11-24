-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_range_trD
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.range_trD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:25.511726+00:00
-- url     : https://prove2.me/theorems/51d6b04a-cc93-4a62-a052-59dda3d855f2
-- title:
--   discriminant Group Counts: range tr D
-- statement:
--   The discriminant Group Counts construction uses the range tr D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L65-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L65-L99

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.range_trD (hd : ∀ i, star (d i) = d i) {θ e : A} (he : (θ - star θ) * e = 1) :
    (trD d).range = hermD d := by sorry
