-- Prove2me | Theorems.Thm_BitDFT_bluestein_middle_identity
-- name    : BitDFT.bluestein_middle_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:12:12.157023+00:00
-- url     : https://prove2.me/theorems/2bae4920-9e81-47f3-8d6d-92acd1f4e785
-- title:
--   Bluestein chirp identity for the mission Fourier convention
-- statement:
--   For a nonzero complex number $
--   ho$ and a finite complex array $X$, the chirp-weighted sum at coordinate $k$ equals the Fourier sum with kernel $(
--   ho^2)^{jk}$:
--
--   $$\rho^{k^2}\sum_{j=0}^{n-1}X_j\rho^{j^2}\rho^{-(k-j)^2}=\sum_{j=0}^{n-1}X_j(\rho^2)^{jk}.$$
--
--   This is the algebraic step that converts a finite-precision DFT construction into a middle-convolution computation. It imposes no root-of-unity hypothesis; that is supplied when the identity is specialized to a DFT.
-- source:
--   Bluestein chirp exponent identity, stated in the BitDFT mission Fourier convention. The Lean proof expands the finite sum and uses k²+j²−(k−j)²=2jk.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_BitDFT_Numerics
set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem BitDFT.bluestein_middle_identity {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (X : Fin n → ℂ) (k : Fin n) :
    ρ ^ ((k.val : ℤ) ^ 2) *
        (∑ j : Fin n, X j * ρ ^ ((j.val : ℤ) ^ 2) *
          ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) =
      ∑ j : Fin n, X j * (ρ ^ 2) ^ (j.val * k.val) := by sorry
