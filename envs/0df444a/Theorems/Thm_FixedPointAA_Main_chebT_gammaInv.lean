-- Prove2me | Theorems.Thm_FixedPointAA_Main_chebT_gammaInv
-- name    : FixedPointAA.Main.chebT_gammaInv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:07.074825+00:00
-- url     : https://prove2.me/theorems/65823a6f-6688-4c87-b497-d2e7bb7feeae
-- title:
--   p. 3 after Eq. (15) — Chebyshev normalization identity
-- statement:
--   For every $0<\delta\le1$ and integer $L\ge1$, take the positive real branch $\gamma^{-1}=\cosh(\operatorname{arcosh}(1/\delta)/L)$. Then
--
--   $$T_L(1/\gamma)=1/\delta.$$
--
--   The paper uses this normalization at the end of the proof of Eq. (1). The identity itself holds for every positive integer $L$, including even degrees.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 3, after Eq. (15)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main

/-- The identity `T_L(1/γ) = 1/δ` used at the end of p. 3. -/
theorem chebT_gammaInv (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) :
    chebT L (gammaInv L δ) = 1 / δ := by sorry

end FixedPointAA.Main
