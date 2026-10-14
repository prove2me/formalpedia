-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_conv_le_aux
-- name    : DbarRegularity.eLpNorm_conv_le_aux
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:24:55.175908+00:00
-- url     : https://prove2.me/theorems/de9b36f1-489c-4f46-abba-1cce606abb1e
-- title:
--   $L^2$ estimate $\|K*f\|_2\le B\|f\|_2+2\|K-K'\|_2\|f\|_1$ for $f\in L^1\cap L^2$ and compactly supported continuous $K'$
-- statement:
--   Let $d\ge0$, $B\in\mathbb R$, and let $K\in L^2(\mathbb R^d)$ be complex valued whose $L^2$ Fourier transform $\hat K$ satisfies $|\hat K(\xi)|\le B$ for almost every $\xi$. Let $f\in L^1\cap L^2(\mathbb R^d)$ and let $K'$ be a continuous, compactly supported function (in particular $K'\in L^2$). Then
--   $$\Big\|\,x\mapsto\int K(x-y)f(y)\,dy\,\Big\|_{L^2}\;\le\;B\,\|f\|_{L^2}+2\,\|K-K'\|_{L^2}\,\|f\|_{L^1}.$$
--
--   Since compactly supported continuous functions are dense in $L^2$, the error term can be made arbitrarily small.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $\hat K$ is `Lp.fourierTransformₗᵢ` applied to `hK.toLp K`; the bound $B$ enters as `ENNReal.ofReal B`. The integral is the Bochner integral and norms are `eLpNorm` in `ℝ≥0∞`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Fourier.LpSpace

namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- The `L²` bound for `f ∈ L¹ ∩ L²`, up to an error controlled by a compactly supported
continuous approximation `K'` of `K`. -/
theorem eLpNorm_conv_le_aux {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (K' : EuclideanSpace ℝ (Fin d) → ℂ) (hK'c : Continuous K') (hK's : HasCompactSupport K')
    (hK'2 : MemLp K' 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume +
        2 * (eLpNorm (K - K') 2 volume * eLpNorm f 1 volume) := by sorry

end DbarRegularity
