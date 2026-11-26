-- Prove2me | Theorems.Thm_Auto_fourier_convolutionAlongVector
-- name    : Auto.fourier_convolutionAlongVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:15.64059+00:00
-- url     : https://prove2.me/theorems/0e0ec43e-066f-5f45-be2c-4cb4bd739dc2
-- title:
--   Auto: fourier convolution Along Vector
-- statement:
--   **Proposition (Properties of convolution along a vector).**
--
--   For $\rho \in W_0(\mathbb{R}^n), \varphi\in W_0(\mathbb{R}), \alpha,\xi\in\mathbb{R}^n$ we have
--   $\rho *_\alpha \varphi\in W_0(\mathbb{R}^n)$ and
--
--   $$
--   \widehat{\rho *_\alpha \varphi}(\xi) = \widehat{\rho}(\xi)\widehat{\varphi}(\alpha\cdot\xi).
--   $$
--
--   See also `Auto.memW0_convolutionAlongVector`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L198-L296
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L198-L296

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

theorem Auto.fourier_convolutionAlongVector {n : ℕ}
    {rho : EuclideanSpace ℝ (Fin n) → ℂ} {phi : ℝ → ℂ}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha xi : EuclideanSpace ℝ (Fin n)) :
    FourierTransform.fourier (convolutionAlongVector rho phi alpha) xi =
      FourierTransform.fourier rho xi *
        FourierTransform.fourier phi (inner ℝ alpha xi) := by sorry
