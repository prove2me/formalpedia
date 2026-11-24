-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_hermD_sq
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.card_hermD_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:05.428612+00:00
-- url     : https://prove2.me/theorems/03a27af1-ee80-4bac-ac9e-0d23dc791da9
-- title:
--   discriminant Group Counts: card herm D sq
-- statement:
--   The discriminant Group Counts construction uses the card herm D sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L101-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L101-L156

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.card_hermD_sq [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1) : Nat.card (hermD d) ^ 2 = Nat.card (entD d) := by sorry
