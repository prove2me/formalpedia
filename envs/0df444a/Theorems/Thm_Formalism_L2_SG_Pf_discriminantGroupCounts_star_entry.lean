-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_star_entry
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.star_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:26.637393+00:00
-- url     : https://prove2.me/theorems/c1300e1c-91cd-4b97-b19e-a53be7c87f9b
-- title:
--   discriminant Group Counts: star entry
-- statement:
--   The discriminant Group Counts construction uses the star entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L44-L47

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.star_entry (hd : ∀ i, star (d i) = d i) {a : A} {i j : m} (h : d i * a * d j = 0) :
    d j * star a * d i = 0 := by sorry
