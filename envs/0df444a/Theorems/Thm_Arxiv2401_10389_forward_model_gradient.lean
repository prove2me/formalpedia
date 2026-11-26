-- Prove2me | Theorems.Thm_Arxiv2401_10389_forward_model_gradient
-- name    : Arxiv2401_10389.forward_model_gradient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:14:38.863394+00:00
-- url     : https://prove2.me/theorems/065e0f3d-8f8c-406b-80b4-14f7c82f8790
-- title:
--   Eq. (10): the gradient of the forward model is $\operatorname{diag}(Hu)+\operatorname{diag}(u)H$
-- statement:
--   In the setting of eq. (6), the forward model $u\mapsto\hat M(\Gamma,u)=u\circ Hu$, a map $\mathbb{C}^{N_e}\to\mathbb{C}^{N_e}$, is differentiable at every $u$, and its derivative is the $N_e\times N_e$ matrix
--
--   $$\nabla_u\hat M(\Gamma,u)=\operatorname{diag}(Hu)+\operatorname{diag}(u)H.$$
--
--   This matrix describes how the received signal on each element varies with the aberration, and it is the building block of the linear operator $K$ of eq. (13a).
--
--   **Formalization Note** The derivative is the complex (holomorphic) Fréchet derivative. $\hat M$ is a polynomial in $u$ that does not involve $\bar u$, so this is the meaning of the paper's gradient as a complex matrix. The paper does not state which derivative it means.
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), claim c002; Section II.B, eqs. (8)-(10), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2401_10389_Basic

open Matrix Filter Topology Asymptotics

namespace Arxiv2401_10389

theorem forward_model_gradient {Ne Ns : ℕ} (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u : Fin Ne → ℂ) :
    HasFDerivAt (forwardModel R γ T)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (forwardGradient R γ T u))) u := by sorry

end Arxiv2401_10389
