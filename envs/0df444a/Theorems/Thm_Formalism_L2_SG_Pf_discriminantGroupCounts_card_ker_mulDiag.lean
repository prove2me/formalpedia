-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_ker_mulDiag
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_mulDiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:41.294248+00:00
-- url     : https://prove2.me/theorems/3956f68c-9c40-49b3-8ca5-dc7289ec084b
-- title:
--   discriminant Group Counts: card ker mul Diag
-- statement:
--   The discriminant Group Counts construction uses the card ker mul Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L158-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L158-L175

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_mulDiag [Finite A] (d : m → A) :
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker =
      ∏ _i : m, ∏ j : m, Nat.card {a : A // a * d j = 0} := by sorry
