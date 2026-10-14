-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_conv_le_of_integrable
-- name    : DbarRegularity.eLpNorm_conv_le_of_integrable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:27:46.746527+00:00
-- url     : https://prove2.me/theorems/43d070f7-26b6-4cf5-90df-8306782bf3eb
-- title:
--   $\|K*f\|_{L^2}\le B\|f\|_{L^2}$ for $f\in L^1\cap L^2(\mathbb R^d)$ when $K\in L^2$ and $|\hat K|\le B$
-- statement:
--   Let $d\ge0$, $B\in\mathbb R$, and let $K\in L^2(\mathbb R^d)$ be complex valued whose $L^2$ Fourier transform satisfies $|\hat K(\xi)|\le B$ for almost every $\xi$. Then for every $f\in L^1\cap L^2(\mathbb R^d)$
--   $$\Big\|\,x\mapsto\int_{\mathbb R^d}K(x-y)f(y)\,dy\,\Big\|_{L^2}\;\le\;B\,\|f\|_{L^2}.$$
--
--   This is the $L^2$ boundedness of convolution with $K$ on the dense subspace $L^1\cap L^2$, with operator norm at most $\sup|\hat K|$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $\hat K$ is `Lp.fourierTransformₗᵢ` applied to `hK.toLp K`, and $B$ enters as `ENNReal.ofReal B`; norms are `eLpNorm` in `ℝ≥0∞`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Fourier.LpSpace

namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- The `L²` bound for `f ∈ L¹ ∩ L²`. -/
theorem eLpNorm_conv_le_of_integrable {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume)
    (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by sorry

end DbarRegularity
