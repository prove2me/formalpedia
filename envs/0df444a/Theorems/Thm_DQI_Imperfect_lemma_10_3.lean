-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_3
-- name    : DQI.Imperfect.lemma_10_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:58.494066+00:00
-- url     : https://prove2.me/theorems/e04b66a1-c767-4888-b063-a8362151e91b
-- title:
--   Lemma 10.3 — average ideal objective matrix
-- statement:
--   For any binary matrix $B\in\mathbb F_2^{m\times n}$ and $\ell\le m$, choose $v\in\mathbb F_2^m$ uniformly. The ideal objective matrix from (147) has average
--
--   $$
--   \mathbb E_v\bar A^{(m,\ell)}=A^{(m,\ell,0)},
--   $$
--
--   where $A^{(m,\ell,0)}$ is the tridiagonal matrix in (70), with adjacent entry $a_k=\sqrt{k(m-k+1)}$ and zero diagonal. This identifies the average ideal matrix without a distance condition.
--
--   **Formalization Note** Uniform expectation is the sum over all $2^m$ binary vectors divided by $2^m$; $\ell\le m$ ensures the shell normalizations are defined.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 38, Lemma 10.3

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_3 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ((1 / ((2 : ℝ) ^ m)) •
      (∑ v : Fin m → ZMod 2, Abar B v ℓ)) = DQI.Semicircle.Atri m ℓ 0 := by sorry

end DQI.Imperfect
