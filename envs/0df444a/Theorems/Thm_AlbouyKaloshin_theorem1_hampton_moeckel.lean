-- Prove2me | Theorems.Thm_AlbouyKaloshin_theorem1_hampton_moeckel
-- name    : AlbouyKaloshin.theorem1_hampton_moeckel
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:49:09.325076+00:00
-- url     : https://prove2.me/theorems/ae4d702c-3fb5-4bcd-a792-d92d82f24037
-- title:
--   Theorem 1 (Hampton–Moeckel): finiteness of four-body central configurations
-- statement:
--   Let $m_1,m_2,m_3,m_4>0$. Then the planar four-body problem with these masses has only finitely many positive normalized central configurations: configurations $(x_k,y_k)\in\mathbb R^2$ with pairwise positive distances $r_{kl}$ satisfying
--   $$
--   \begin{pmatrix}x_k\\y_k\end{pmatrix}=\sum_{l\ne k}m_l\,r_{kl}^{-3}\begin{pmatrix}x_k-x_l\\y_k-y_l\end{pmatrix}\quad(k=1,\dots,4),\qquad y_{12}=0.
--   $$
--   This answers Smale's 6th problem for $n=4$; the paper obtains it from Theorem 5.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 536, Theorem 1 (Definition 1, p. 536)

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem theorem1_hampton_moeckel (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k) :
    (PosNormalizedCC 4 m).Finite := by sorry

end AlbouyKaloshin
