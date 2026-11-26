-- Prove2me | Theorems.Thm_Arxiv2405_00432_retardance_from_mueller_matrix
-- name    : Arxiv2405_00432.retardance_from_mueller_matrix
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:53:32.467777+00:00
-- url     : https://prove2.me/theorems/6c1da521-f973-414f-8bb5-2f8f948b0ea0
-- title:
--   Eqs. (13)-(14): the retardance from the Mueller matrix of a retarder at 0° (as proved)
-- statement:
--   Let $M_T(\delta,\theta)$ be the retarder Mueller matrix of eq. (11). Then
--   $$M_T(\delta,0)=\begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&\cos\delta&-\sin\delta\\0&0&\sin\delta&\cos\delta\end{pmatrix}$$
--   (eq. (13)), and if $-\pi/2<\delta<\pi/2$, each of the four values of eq. (14) computed from $m=M_T(\delta,0)$,
--   $$\delta_1=\tan^{-1}\Big(-\frac{m_{34}}{m_{33}}\Big),\ \delta_2=\tan^{-1}\Big(-\frac{m_{34}}{m_{44}}\Big),\ \delta_3=\tan^{-1}\Big(\frac{m_{43}}{m_{33}}\Big),\ \delta_4=\tan^{-1}\Big(\frac{m_{43}}{m_{44}}\Big),$$
--   equals $\delta$.
--
--   **Formalization Note** The paper says that $\delta=\tan^{-1}(\sin\delta/\cos\delta)$ gives the correct sign and magnitude of the retardance, without restricting $\delta$. With the real (single-argument) arctangent this holds only for $-\pi/2<\delta<\pi/2$; for example $\delta=3\pi/4$ gives $\delta_1=\cdots=\delta_4=-\pi/4$. The statement is therefore restricted to that range, which is what the paper's argument establishes (title "as proved").
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), claim c009; Section 4.1, eq. (11), PDF p. 9; Section 4.2, eqs. (13), (14), PDF pp. 11-12

import Mathlib
import Definitions.Def_Arxiv2405_00432_Basic

open Matrix

namespace Arxiv2405_00432

theorem retardance_from_mueller_matrix (δ : ℝ) :
    retarderMueller δ 0 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Real.cos δ, -Real.sin δ;
      0, 0, Real.sin δ, Real.cos δ] ∧
    (-(Real.pi / 2) < δ → δ < Real.pi / 2 →
      ∀ k : Fin 4, retardanceEst (retarderMueller δ 0) k = δ) := by sorry

end Arxiv2405_00432
