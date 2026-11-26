-- Prove2me | Theorems.Thm_Auto_memW0_convolutionAlongVector
-- name    : Auto.memW0_convolutionAlongVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:03.976584+00:00
-- url     : https://prove2.me/theorems/5b95f45e-c7b2-4d6c-ac83-67126d24bb3f
-- title:
--   Auto: mem W0 convolution Along Vector
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
--   See also `Auto.fourier_convolutionAlongVector`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L164-L184
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L164-L184

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

theorem Auto.memW0_convolutionAlongVector {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {rho : EuclideanSpace ℝ (Fin n) → 𝕜} {phi : ℝ → 𝕜}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha : EuclideanSpace ℝ (Fin n)) :
    MemW0 (convolutionAlongVector rho phi alpha) := by sorry
