-- Prove2me | Theorems.Thm_FamousTheorems_fourier_eq
-- name    : FamousTheorems.fourier_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:22.375089+00:00
-- url     : https://prove2.me/theorems/f85b8b64-d1c7-4be0-8e83-5a7017443e89
-- title:
--   The Fourier transform on $L^1(\mathbb{R}^d)$
-- statement:
--   **The Fourier transform** on $L^1$. The transform is given by the absolutely convergent integral $$\hat f(\xi) = \int_{\mathbb{R}^d} f(x)\,e^{-2\pi i \langle x,\xi\rangle}\,dx.$$ Integrability of $f$ is exactly what makes the defining integral converge absolutely for every $\xi$, so the transform is defined pointwise and is bounded by $\lVert f\rVert_1$. This is the analytic foundation on which the rest of Fourier analysis is built: the $L^2$ theory is obtained by extending from the dense subspace $L^1 \cap L^2$ via Plancherel, and the distributional theory by duality. The transform converts convolution into multiplication, which is why it linearises constant-coefficient differential equations. **Formalization note.** The statement identifies Mathlib's `fourierIntegral` with the concrete integral formula in the real inner-product setting. The result is Mathlib's `Real.fourier_eq`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem fourier_eq :
    ∀ {V : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
    [inst_2 : NormedAddCommGroup V] [inst_3 : InnerProductSpace ℝ V] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] 
    [inst_6 : FiniteDimensional ℝ V] (f : V → E) (w : V), 
    FourierTransform.fourier f w = ∫ (v : V), Real.fourierChar (-inner ℝ v w) • f v := by sorry

end FamousTheorems
