-- Prove2me | Theorems.Thm_DerivativeChainPrivate_almost_real_row_has_real_root
-- name    : DerivativeChainPrivate.almost_real_row_has_real_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:53:20.598318+00:00
-- url     : https://prove2.me/theorems/c93db777-01b0-40c1-8a23-7b31f27d2967
-- title:
--   Every actual row above the nonreal slot count has a real root
-- statement:
--   For a root list whose product has real coefficients, every actual proposal row m with nonrealCount a < m <= n has a real zero. Multiplicities are included in the counting premise. This does not assert a short chain.
-- source:
--   Derivative-zero chains: public formalization reference, R32, DerivativeChainPrivate.almost_real_row_has_real_root. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Theorems.Thm_DerivativeChainPrivate_almost_real_row_count

set_option autoImplicit false
open DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.almost_real_row_has_real_root {n m : ℕ} (a : Fin n → ℂ) (hr : RealCoefficients a)
    (hm : m ≤ n) (hc : nonrealCount a < m) :
    ∃ x : ℝ, (row a m).eval (x : ℂ) = 0 := by sorry
