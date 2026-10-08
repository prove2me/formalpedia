-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_splitting_resolvent_firmly_nonexpansive
-- name    : DouglasRachfordPPA.GenDR.splitting_resolvent_firmly_nonexpansive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:23:34.361646+00:00
-- url     : https://prove2.me/theorems/9856d02c-6bc9-45c2-bb42-7dc8bc08a0bb
-- title:
--   Corollary 4.1 — $(I+S_{\lambda,A,B})^{-1}$ is firmly nonexpansive with full domain
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\lambda>0$, and $A,B$ maximal monotone operators on $\mathcal H$. Then the resolvent $(I+S_{\lambda,A,B})^{-1}$ of the splitting operator is firmly nonexpansive and has full domain.
--
--   By Theorem 6 this resolvent is the Douglas–Rachford map $G_{\lambda,A,B}=J_{\lambda A}\circ(2J_{\lambda B}-I)+(I-J_{\lambda B})$, so the corollary is the Lions–Mercier result that $G_{\lambda,A,B}$ is firmly nonexpansive.
--
--   **Formalization Note** The resolvent is the graph resolvent with $c=1$, `opResolvent 1 (splittingOp lam A B)`; firm nonexpansiveness is the graph notion and "full domain" is $\operatorname{dom}=\mathcal H$. The identification with $G_{\lambda,A,B}$ is stated separately in Theorem 6.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 17, Corollary 4.1

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Corollary 4.1: for `lam > 0` and maximal monotone `A`, `B`, the resolvent
`(I + S_{lam,A,B})⁻¹` of the splitting operator is firmly nonexpansive and has full domain. -/
theorem splitting_resolvent_firmly_nonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) :
    IsFirmlyNonexpansiveOp (opResolvent 1 (splittingOp lam A B)) ∧
    dom (opResolvent 1 (splittingOp lam A B)) = Set.univ := by sorry

end DouglasRachfordPPA.GenDR
