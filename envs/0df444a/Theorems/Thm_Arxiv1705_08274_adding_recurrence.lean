-- Prove2me | Theorems.Thm_Arxiv1705_08274_adding_recurrence
-- name    : Arxiv1705_08274.adding_recurrence
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T02:14:28.246567+00:00
-- url     : https://prove2.me/theorems/5ffb5766-07ae-42d6-9221-c6284e5a6d84
-- title:
--   Eqs. (28a)-(29a): the adding recurrence for a composite and a node
-- statement:
--   Let a composite of $l-1$ nodes have response $Q_{l-1}=\begin{bmatrix}Q_1&Q_2\\Q_2&Q_1\end{bmatrix}$ in the symmetric form (25b), and let the added node have response $\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$. All blocks are of order $2N$ and otherwise arbitrary; the paper allows the added piece to be a composite. Let $w_m=\begin{bmatrix}I&-Q_2\\-R_f&I\end{bmatrix}$ be invertible, $w_p=\begin{bmatrix}0&Q_1\\T_n&0\end{bmatrix}$, $U_l=w_m^{-1}w_p$, and
--
--   $$Q_l=\begin{bmatrix}0&Q_1\\T_n&0\end{bmatrix}U_l+\begin{bmatrix}0&Q_2\\R_f&0\end{bmatrix}.$$
--
--   If intensities satisfy (25a), $[I^-_0;I^+_{l-1}]=Q_{l-1}[I^-_{l-1};I^+_0]$, and (26a), $[I^-_{l-1};I^+_l]=\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}[I^-_l;I^+_{l-1}]$, then
--
--   $$\begin{bmatrix}I^+_{l-1}\\I^-_{l-1}\end{bmatrix}=U_l\begin{bmatrix}I^-_l\\I^+_0\end{bmatrix}\ \ (28a),\qquad \begin{bmatrix}I^-_0\\I^+_l\end{bmatrix}=Q_l\begin{bmatrix}I^-_l\\I^+_0\end{bmatrix}\ \ (28e).$$
--
--   In blocks, with $U_l=\begin{bmatrix}U_{l,1}&U_{l,2}\\U_{l,3}&U_{l,4}\end{bmatrix}$,
--
--   $$Q_l=\begin{bmatrix}Q_1U_{l,3}&Q_1U_{l,4}+Q_2\\T_nU_{l,1}+R_f&T_nU_{l,2}\end{bmatrix}\quad(29a).$$
--
--   **Formalization Note** The block numbering $U_{l,1},\dots,U_{l,4}$ is read as $(1,1),(1,2),(2,1),(2,2)$, which is the only reading under which (29a) follows from (28d). The right-hand side of (27a) is used with the signs that follow from (26b), $+Q_1$ and $+T_n$; the printed minus signs are a misprint. The symmetric form (25b) of the composite is a hypothesis, as in the paper. It need not hold for a heterogeneous composite (see the mission report).
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c004; Section I.D, eqs. (25a), (25b), (26a), (26b), (27a,b), (28a)-(28e), (29a), PDF pp. 12-14

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem adding_recurrence {N : ℕ} (Q₁ Q₂ Tn Rf : Matrix (Dir N) (Dir N) ℝ)
    (hw : IsUnit (wMinus Q₂ Rf).det)
    (I0m I0p Ilm Ilp Ilm1 Ilp1 : Dir N → ℝ)
    (hcomp : Sum.elim I0m Ilp1 = fromBlocks Q₁ Q₂ Q₂ Q₁ *ᵥ Sum.elim Ilm1 I0p)
    (hnode : Sum.elim Ilm1 Ilp = fromBlocks Tn Rf Rf Tn *ᵥ Sum.elim Ilm Ilp1) :
    Sum.elim Ilp1 Ilm1 = addU Q₁ Q₂ Tn Rf *ᵥ Sum.elim Ilm I0p ∧
    Sum.elim I0m Ilp = addQ Q₁ Q₂ Tn Rf *ᵥ Sum.elim Ilm I0p ∧
    addQ Q₁ Q₂ Tn Rf =
      fromBlocks (Q₁ * (addU Q₁ Q₂ Tn Rf).toBlocks₂₁) (Q₁ * (addU Q₁ Q₂ Tn Rf).toBlocks₂₂ + Q₂)
        (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₁ + Rf) (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₂) := by sorry

end Arxiv1705_08274
