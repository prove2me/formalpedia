-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_ker_eq_card_hermD
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_eq_card_hermD
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:32.64869+00:00
-- url     : https://prove2.me/theorems/7094a80f-5279-480a-b79c-e99358c1969a
-- title:
--   discriminant Group Counts: card ker eq card herm D
-- statement:
--   The discriminant Group Counts construction uses the card ker eq card herm D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L177-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L177-L189

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_eq_card_hermD [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) :
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker = Nat.card (hermD d) := by sorry
