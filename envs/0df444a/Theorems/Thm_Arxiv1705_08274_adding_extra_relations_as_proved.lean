-- Prove2me | Theorems.Thm_Arxiv1705_08274_adding_extra_relations_as_proved
-- name    : Arxiv1705_08274.adding_extra_relations_as_proved
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T02:16:20.910889+00:00
-- url     : https://prove2.me/theorems/54878346-f4cb-47e6-b6a5-bff48c2fafa8
-- title:
--   Eq. (29b) (as proved): relations among the blocks of $U_l$ under symmetry
-- statement:
--   In the setting of the adding recurrence (29a), with $Q_{l-1}=\begin{bmatrix}Q_1&Q_2\\Q_2&Q_1\end{bmatrix}$, node response $\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$ and $w_m$ invertible, suppose the combined response $Q_l$ is itself symmetric: $Q_{l,1}=Q_{l,4}$ and $Q_{l,2}=Q_{l,3}$. If $Q_1=Q_{l-1,1}$ is invertible, then the blocks of $U_l$ satisfy
--
--   $$U_{l,3}=Q_{l-1,1}^{-1}T_nU_{l,2},\qquad U_{l,4}=Q_{l-1,1}^{-1}\big[T_nU_{l,1}+R_f-Q_{l-1,2}\big].$$
--
--   **Formalization Note** The paper prints (29b) with $Q_{l,1}^{-1}$ and $Q_{l,2}$ in place of $Q_{l-1,1}^{-1}$ and $Q_{l-1,2}$, and says only that the relations were numerically verified. Equating the blocks of (29a) gives the relations stated here. The printed version fails numerically, for example when a node is doubled.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c005; Section I.D, eq. (29b), PDF p. 14; derived from eq. (29a)

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem adding_extra_relations_as_proved {N : ℕ} (Q₁ Q₂ Tn Rf : Matrix (Dir N) (Dir N) ℝ)
    (hw : IsUnit (wMinus Q₂ Rf).det) (hQ₁ : IsUnit Q₁.det)
    (hsym : IsSymmetricResponse (addQ Q₁ Q₂ Tn Rf)) :
    (addU Q₁ Q₂ Tn Rf).toBlocks₂₁ = Q₁⁻¹ * Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₂ ∧
    (addU Q₁ Q₂ Tn Rf).toBlocks₂₂ = Q₁⁻¹ * (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₁ + Rf - Q₂) := by sorry

end Arxiv1705_08274
