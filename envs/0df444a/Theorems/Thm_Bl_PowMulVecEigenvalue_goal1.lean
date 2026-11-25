-- Prove2me | Theorems.Thm_Bl_PowMulVecEigenvalue_goal1
-- name    : Bl.PowMulVecEigenvalue.goal1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:02.977716+00:00
-- url     : https://prove2.me/theorems/7511519c-f85b-52a2-8942-779bbcab6174
-- title:
--   Pow Mul Vec Eigenvalue: goal1
-- statement:
--   The Pow Mul Vec Eigenvalue construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowMulVecEigenvalue/PowMulVecEig.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PowMulVecEigenvalue/PowMulVecEig.lean#L15-L30

import Mathlib
import Definitions.Def_Lemmata_PowMulVecEigenvalue_PowMulVecEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.PowMulVecEigenvalue

theorem Bl.PowMulVecEigenvalue.goal1 :
  ∀ {S : Type u_1} [inst : CommRing.{u_1} S] {n : Type u_2} [inst_1 : Fintype.{u_2} n] [inst_2 : DecidableEq.{u_2 + 1} n]
  (Q : Matrix.{u_2, u_2, u_1} n n S) (μ : S) (v : n → S),
  Eq.{max (u_1 + 1) (u_2 + 1)} (Matrix.mulVec.{u_1, u_2, u_2} Q v) (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} μ v) →
    ∀ (p : Polynomial.{0} Int),
      Eq.{max (u_1 + 1) (u_2 + 1)}
        (Matrix.mulVec.{u_1, u_2, u_2}
          (DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) 1, 1, max (u_1 + 1) (u_2 + 1)}
            (Polynomial.aeval.{0, max u_1 u_2} Q) p)
          v)
        (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2}
          (DFunLike.coe.{max (u_1 + 1) 1, 1, u_1 + 1} (Polynomial.aeval.{0, u_1} μ) p) v) := by sorry
