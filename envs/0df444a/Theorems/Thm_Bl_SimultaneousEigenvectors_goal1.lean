-- Prove2me | Theorems.Thm_Bl_SimultaneousEigenvectors_goal1
-- name    : Bl.SimultaneousEigenvectors.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:28.926493+00:00
-- url     : https://prove2.me/theorems/6cac268e-276d-4d6c-9528-62629f8b08b3
-- title:
--   Simultaneous Eigenvectors: goal1
-- statement:
--   The Simultaneous Eigenvectors construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/SimultaneousEigenvectors/BlSimeig.lean#L67-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/SimultaneousEigenvectors/BlSimeig.lean#L67-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.SimultaneousEigenvectors

theorem Bl.SimultaneousEigenvectors.goal1 :
  ∀ {n : Nat} {X : Type u_1} [inst : NormedAddCommGroup.{u_1} X] [inst_1 : InnerProductSpace.{0, u_1} Complex X]
  {A : Fin n → Fin n → Module.End.{0, u_1} Complex X},
  ReciprocityTheory.ChartRestriction.DS.IsGlRep.{u_1} A →
    ∀ (s : Finset.{0} (Fin n)) (T : Submodule.{0, u_1} Complex X),
      FiniteDimensional.{0, u_1} Complex (Subtype.{u_1 + 1} fun (x : X) ↦ Membership.mem.{u_1, u_1} T x) →
        (∀ (c : Fin n) (v : X),
            Membership.mem.{u_1, u_1} T v →
              Membership.mem.{u_1, u_1} T (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (A c c) v)) →
          Ne.{u_1 + 1} T Bot.bot.{u_1} →
            Exists.{u_1 + 1} fun (w : X) ↦
              And (Membership.mem.{u_1, u_1} T w)
                (And (Ne.{u_1 + 1} w 0)
                  (Exists.{1} fun (μ : Fin n → Complex) ↦
                    ∀ (c : Fin n),
                      Membership.mem.{0, 0} s c →
                        Eq.{u_1 + 1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (A c c) w)
                          (HSMul.hSMul.{0, u_1, u_1} (μ c) w))) := by sorry
