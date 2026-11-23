-- Prove2me | Theorems.Thm_Bl_PartialDerivativeDegree_goal1
-- name    : Bl.PartialDerivativeDegree.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:17.658964+00:00
-- url     : https://prove2.me/theorems/bfccb3c5-1426-4189-9f0a-5bc4a12ee722
-- title:
--   Partial Derivative Degree: goal1
-- statement:
--   The Partial Derivative Degree construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PartialDerivativeDegree/PderivTdSuccLe.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/PartialDerivativeDegree/PderivTdSuccLe.lean#L26-L40

import Mathlib
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.PartialDerivativeDegree

theorem Bl.PartialDerivativeDegree.goal1 :
  ∀ {σ : Type u_1} (i : σ) (q L : MvPolynomial.{u_1, 0} σ Complex),
  LE.le.{0} (MvPolynomial.totalDegree.{0, u_1} L) 1 →
    LE.le.{0}
      (MvPolynomial.totalDegree.{0, u_1}
        (HMul.hMul.{u_1, u_1, u_1}
          (DFunLike.coe.{max (u_1 + 1) 1, max (u_1 + 1) 1, max (u_1 + 1) 1} (MvPolynomial.pderiv.{0, u_1} i) q) L))
      (MvPolynomial.totalDegree.{0, u_1} q) := by sorry
