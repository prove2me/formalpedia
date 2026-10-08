-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_zeros_of_splitting_operator
-- name    : DouglasRachfordPPA.GenDR.zeros_of_splitting_operator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:23:35.132146+00:00
-- url     : https://prove2.me/theorems/862d69ba-d00e-4c8b-9bd7-e2dddb5955f8
-- title:
--   Theorem 5 — $\mathrm{zer}(S_{\lambda,A,B})=Z^*_\lambda\subseteq\{u+\lambda b\mid u\in\mathrm{zer}(A+B),\,b\in Bu\}$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\lambda>0$, and $A,B$ arbitrary operators on $\mathcal H$. Then
--   $$\operatorname{zer}(S_{\lambda,A,B})=Z^*_\lambda=\{u+\lambda b\mid b\in Bu,\ -b\in Au\}\subseteq\{u+\lambda b\mid u\in\operatorname{zer}(A+B),\ b\in Bu\}.$$
--
--   No monotonicity is assumed. The theorem says that every zero $z=u+\lambda b$ of the splitting operator yields a zero $u$ of $A+B$, which is why the iterates of Douglas–Rachford splitting carry information about $\operatorname{zer}(A+B)$.
--
--   **Formalization Note** $A+B$ is the graph sum, so $u\in\operatorname{zer}(A+B)$ means $0=a+b'$ for some $a\in Au$, $b'\in Bu$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), pp. 17–18, Theorem 5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Theorem 5: for `lam > 0` and any operators `A`, `B`,
`zer(S_{lam,A,B}) = Z*_lam ⊆ {u + lam b | u ∈ zer(A + B), b ∈ B u}`. -/
theorem zeros_of_splitting_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H) :
    zer (splittingOp lam A B) = Zstar lam A B ∧
    Zstar lam A B ⊆ {z | ∃ u b : H, u ∈ zer (opAdd A B) ∧ b ∈ B u ∧ z = u + lam • b} := by sorry

end DouglasRachfordPPA.GenDR
