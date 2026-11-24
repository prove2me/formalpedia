-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_kerX_eq
-- name    : Formalism.L2.SG.Pf.discriminantGroupCounts.card_kerX_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:58.573397+00:00
-- url     : https://prove2.me/theorems/68ad3bc1-a518-4688-8d7b-5709b1503aeb
-- title:
--   discriminant Group Counts: card ker X eq
-- statement:
--   The discriminant Group Counts construction uses the card ker X eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L191-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean#L191-L288

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

theorem Formalism.L2.SG.Pf.discriminantGroupCounts.card_kerX_eq [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) (N : ℕ)
    (hN : ∀ T ∈ tSet d, Nat.card {Y : Matrix m m A // phiH (diagonal d) Y = T} = N) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal d * X = diagonal d ∧ ∃ Y, X = 1 + Y * diagonal d} =
      N := by sorry
