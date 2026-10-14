-- Prove2me | Theorems.Thm_DbarRegularity_convolution_l2_bound
-- name    : DbarRegularity.convolution_l2_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:30:43.150589+00:00
-- url     : https://prove2.me/theorems/5bc26d5c-7b61-4e30-8a69-5976be5ab417
-- title:
--   $\|K*f\|_{L^2}\le B\|f\|_{L^2}$ on $L^2(\mathbb R^d)$ when $K\in L^2$ has $|\hat K|\le B$
-- statement:
--   Let $d\ge0$, $B\in\mathbb R$, and let $K\in L^2(\mathbb R^d)$ be complex valued whose $L^2$ Fourier transform satisfies $|\hat K(\xi)|\le B$ for almost every $\xi$. Then for every $f\in L^2(\mathbb R^d)$ the convolution $Tf(x)=\int K(x-y)f(y)\,dy$ belongs to $L^2(\mathbb R^d)$ and
--   $$\|Tf\|_{L^2}\;\le\;B\,\|f\|_{L^2}.$$
--
--   This is the $L^2$ theory of convolution operators with bounded Fourier multiplier, for the convolution defined pointwise, which is finite at every point since $K,f\in L^2$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $\hat K$ is `Lp.fourierTransformₗᵢ` applied to `hK.toLp K`, and $B$ enters as `ENNReal.ofReal B`. The convolution is the Bochner integral `∫ y, K (x - y) * f y`; norms are `eLpNorm · 2 volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Fourier.LpSpace

namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- **`L²` bound.** If `K ∈ L²(ℝ^d)` has `L²` Fourier transform bounded by `B`, then
`f ↦ ∫ K(· - y) f(y) dy` maps `L²` to `L²` with norm at most `B`. -/
theorem convolution_l2_bound {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f 2 volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) 2 volume ∧
      eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by sorry

end DbarRegularity
