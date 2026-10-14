-- Prove2me | Theorems.Thm_DbarRegularity_convolution_lp_bound
-- name    : DbarRegularity.convolution_lp_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:53:22.010502+00:00
-- url     : https://prove2.me/theorems/9bb2c951-83a3-4610-83aa-c2b1f3f1c905
-- title:
--   L^p bounds for convolution with a kernel whose Fourier transform is bounded and whose gradient decays like |x|^{-d-1}
-- statement:
--   Let $K\in L^2(\mathbb{R}^d)$ and $B\ge0$. $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Assume
--
--   1. the Fourier transform of $K$ is essentially bounded: $|\hat K(\xi)|\le B$ for almost every $\xi$;
--   2. $K$ is of class $C^1$ on $\mathbb{R}^d\setminus\{0\}$ and $|\nabla K(x)|\le B/|x|^{d+1}$ for $x\ne0$.
--
--   For $f\in L^1\cap L^p$ let $Tf(x)=\int_{\mathbb{R}^d}K(x-y)f(y)\,dy$. Then for every $1<p<\infty$ there is a constant $A_p$, depending only on $p$, $B$ and $d$ (in particular not on the $L^2$ norm of $K$), such that $Tf\in L^p$ and
--   $$\|Tf\|_p\le A_p\|f\|_p\qquad\text{for all }f\in L^1\cap L^p .$$
--
--   **Formalization Note** $\hat K$ is Mathlib's Fourier transform on $L^2$, `Lp.fourierTransformₗᵢ`, applied to `hK.toLp K`; it is normalized as $\hat K(\xi)=\int K(x)e^{-2\pi i x\cdot\xi}dx$, while Stein uses $e^{+2\pi i x\cdot\xi}$; the two differ by $\xi\mapsto-\xi$, which does not change the bound $|\hat K|\le B$. $|\nabla K(x)|$ is written as the operator norm `‖fderiv ℝ K x‖`, which is at most the Euclidean norm of the gradient, so the hypothesis here is implied by Stein's with the same $B$. $Tf(x)$ is the Bochner integral `∫ y, K (x - y) * f y`. The constant `A : ℝ≥0` is chosen before $K$ and $f$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter II, § 2.2, Theorem 1, p. 29

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Fourier.LpSpace

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter II, § 2.2, Theorem 1 (p. 29): let `K ∈ L²(ℝ^d)` with
essentially bounded Fourier transform, `|K̂| ≤ B`, and let `K` be of class `C¹` outside the origin
with `|∇K(x)| ≤ B / |x|^{d+1}`. For `f ∈ L¹ ∩ L^p`, `1 < p < ∞`, the convolution
`T f (x) = ∫ K(x - y) f(y) dy` satisfies `‖T f‖_p ≤ A_p ‖f‖_p`, where `A_p` depends only on `p`,
`B` and `d` (not on the `L²` norm of `K`). -/
theorem convolution_lp_bound (d : ℕ) (p : ℝ) (hp : 1 < p) (B : ℝ) :
    ∃ A : ℝ≥0, ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume),
      (∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B) →
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f 1 volume → MemLp f (ENNReal.ofReal p) volume →
        MemLp (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ∧
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
