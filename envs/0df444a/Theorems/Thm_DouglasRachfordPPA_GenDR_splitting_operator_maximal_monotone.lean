-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_splitting_operator_maximal_monotone
-- name    : DouglasRachfordPPA.GenDR.splitting_operator_maximal_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:41:41.945745+00:00
-- url     : https://prove2.me/theorems/0136bece-8c49-49d7-a616-8f86cc5d7485
-- title:
--   Theorem 4 — the splitting operator $S_{\lambda,A,B}$ is (maximal) monotone
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\lambda>0$, and $A,B$ operators on $\mathcal H$, with splitting operator
--   $$S_{\lambda,A,B}=\{(v+\lambda b,\ u-v)\mid (u,b)\in B,\ (v,a)\in A,\ v+\lambda a=u-\lambda b\}.$$
--
--   1. If $A$ and $B$ are monotone, then $S_{\lambda,A,B}$ is monotone.
--   2. If $A$ and $B$ are maximal monotone, then $S_{\lambda,A,B}$ is maximal monotone.
--
--   This is the structural fact behind the paper's view of Douglas–Rachford splitting as a proximal point method on $S_{\lambda,A,B}$.
--
--   **Formalization Note** $S_{\lambda,A,B}$ is the set formula above (`splittingOp`), not the operator $G^{-1}-I$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 16, Theorem 4

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Theorem 4: for `lam > 0`, if `A` and `B` are monotone then the splitting operator
`S_{lam,A,B}` is monotone; if `A` and `B` are maximal monotone, so is `S_{lam,A,B}`. -/
theorem splitting_operator_maximal_monotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H) :
    (IsMonotoneOp A → IsMonotoneOp B → IsMonotoneOp (splittingOp lam A B)) ∧
    (IsMaximalMonotone A → IsMaximalMonotone B →
      IsMaximalMonotone (splittingOp lam A B)) := by sorry

end DouglasRachfordPPA.GenDR
