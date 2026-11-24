-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injective_fderiv_proj_of_fastPlane_family
-- name    : FiniteEnergyPlane.injective_fderiv_proj_of_fastPlane_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:27:16.583062+00:00
-- url     : https://prove2.me/theorems/288852b6-64b0-4dd7-9398-dce7f1229176
-- title:
--   Curves of leaves through a Reeb trajectory give immersions into the energy level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $P$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. Let $r>0$ and $f:\mathbb{C}\times B_r(0)\to\mathbb{R}^4$ be $C^1$, injective, with injective derivative everywhere, such that every slice $f(\cdot,\tau)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Let $y$ be a Reeb trajectory, $I\subseteq\mathbb{R}$ open and $\zeta,\tau:I\to\mathbb{C}$ differentiable with $\tau(I)\subseteq B_r(0)$ and $f(\zeta(t),\tau(t))=y(t)$ for $t\in I$. Then the map
--   $$I\times\mathbb{C}\to S,\qquad (t,w)\longmapsto \mathrm{pr}_S\,f(w,\tau(t))$$
--   has injective derivative at every point of $I\times\mathbb{C}$.
--
--   It is the immersion property behind the local families of pages of the open book.
--
--   **Formalization Note** $\mathrm{pr}_S$ is `proj H`; the derivative is `fderiv ℝ` of `fun p : ℝ × ℂ => proj H (f (p.2, τ p.1))`. Differentiability of $\zeta,\tau$ is `DifferentiableOn ℝ · I`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Transversality of a curve of leaves to a family of embedded fast planes along a Reeb trajectory.
Let `P` have Conley–Zehnder index at least `3` and let `f : ℂ × B_r(0) → V 1` be `C¹`, injective,
with injective derivative, such that every `f(·, τ)` is an embedded fast finite-energy plane
asymptotic to `P` at `∞`. Let `I ⊆ ℝ` be open, `ζ, τ : I → ℂ` differentiable with `τ(I) ⊆ B_r(0)`
and `f(ζ t, τ t) = y t` for a Reeb trajectory `y`. Then `(t, w) ↦ proj H (f (w, τ t))` has injective
derivative at every point of `I × ℂ`. -/
theorem injective_fderiv_proj_of_fastPlane_family (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (I : Set ℝ) (hI : IsOpen I) (ζ τ : ℝ → ℂ) (hζ : DifferentiableOn ℝ ζ I)
    (hτ : DifferentiableOn ℝ τ I) (hτI : ∀ t ∈ I, τ t ∈ ball (0 : ℂ) r)
    (hfy : ∀ t ∈ I, f (ζ t, τ t) = y t) :
    ∀ t ∈ I, ∀ w : ℂ,
      Function.Injective (fderiv ℝ (fun p : ℝ × ℂ => proj H (f (p.2, τ p.1))) (t, w)) := by
  sorry

end FiniteEnergyPlane
