-- Prove2me | Theorems.Thm_FRBSplitting_Linear_zeroSet_subsingleton
-- name    : FRBSplitting.Linear.zeroSet_subsingleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:21.295084+00:00
-- url     : https://prove2.me/theorems/cd245da9-e3a1-49f2-834d-0a3ed1c9eb85
-- title:
--   Proof of Theorem 2.9, p. 9 — (A + B)⁻¹(0) has at most one element when A is strongly monotone and B monotone
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ $m$-strongly monotone with $m>0$, and $B:H\to H$ monotone. Then the zero set
--   $$(A+B)^{-1}(0)=\{x\in H: 0\in A(x)+B(x)\}$$
--   contains at most one point.
--
--   In Theorem 2.9 this gives the uniqueness of the limit: the zero set is assumed nonempty, so it is a singleton, and the iterates converge to its only element.
--
--   **Formalization Note.** The paper obtains uniqueness at the end of the proof of Theorem 2.9, from the convergence of a single run to every zero. The statement here needs neither the method nor Lipschitz continuity nor maximality, and is stated without them (a stronger statement).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 9, proof of Theorem 2.9, last sentence

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem zeroSet_subsingleton {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (m : ℝ)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hBm : IsMonotoneFun B) :
    (FRBSplitting.Weak.zeroSet A B).Subsingleton := by sorry

end FRBSplitting.Linear
