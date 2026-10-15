-- Prove2me | Theorems.Thm_FixedPointAA_Main_reduction_to_plane
-- name    : FixedPointAA.Main.reduction_to_plane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:02.742304+00:00
-- url     : https://prove2.me/theorems/ef75eb90-c923-41c5-913f-cd02316c209c
-- title:
--   Eq. (4), p. 2 — success amplitude depends only on the initial overlap
-- statement:
--   Let $s,T$ be unit vectors with $\lambda=|\langle T|s\rangle|^2>0$. For arbitrary real phase sequences $\alpha_j,\beta_j$ and any $l\ge0$, form the ordered product $\mathcal S_{2l+1}$. Its target-amplitude magnitude agrees with that of the same product in the two-dimensional basis $|\bar t\rangle,|t\rangle$, starting from $(\sqrt{1-\lambda},\sqrt\lambda)$:
--
--   $$|\langle T|\mathcal S_{2l+1}|s\rangle|=|\langle t|\mathcal S_{2l+1}^{(2)}(\sqrt{1-\lambda},\sqrt\lambda)\rangle|.$$
--
--   This reduction explains why the paper can analyze the product using two-by-two matrices, including the endpoint $\lambda=1$.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 2, Eq. (4)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main
open scoped Matrix

/-- The success-amplitude magnitude is determined by the initial overlap, as in Eq. (4). -/
theorem reduction_to_plane {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (lam : ℝ) (hlam : ‖star T ⬝ᵥ s‖ ^ 2 = lam) (hlam0 : 0 < lam)
    (α β : ℕ → ℝ) (l : ℕ) :
    ‖star T ⬝ᵥ (seqOp s T α β l *ᵥ s)‖ =
      ‖star tVec ⬝ᵥ (seqOp (sVec lam) tVec α β l *ᵥ sVec lam)‖ := by sorry

end FixedPointAA.Main
