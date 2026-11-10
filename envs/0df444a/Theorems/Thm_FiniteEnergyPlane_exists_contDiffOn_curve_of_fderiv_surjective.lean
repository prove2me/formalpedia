-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_curve_of_fderiv_surjective
-- name    : FiniteEnergyPlane.exists_contDiffOn_curve_of_fderiv_surjective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:28:16.315202+00:00
-- url     : https://prove2.me/theorems/8f5e974f-07ab-480d-af4c-a74c99a847d4
-- title:
--   A smooth curve of zeros through a regular zero in a prescribed kernel direction
-- statement:
--   Let $E, F$ be real Banach spaces, $\varepsilon > 0$, and $f : E \to F$ of class $C^\infty$ on the ball $B_\varepsilon(0)$ with $f(0) = 0$ and $Df(0)$ surjective. Let $K$ be a finite-dimensional real normed space and $\pi_0 : E \to K$ a linear map that is injective on $\ker Df(0)$. Then for every $k \in \ker Df(0)$ there are $r > 0$ and a curve $\gamma : \mathbb{R} \to E$, $C^\infty$ on $(-r, r)$, with $\gamma(0) = 0$, $\gamma'(0) = k$, and $\gamma(t) \in B_\varepsilon(0)$, $f(\gamma(t)) = 0$ for all $t \in (-r, r)$.
--
--   **Role.** Produces smooth one-parameter families of solutions of a nonlinear Fredholm problem with finite-dimensional kernel and vanishing cokernel, with prescribed infinitesimal direction.
-- source:
--   Banach-space implicit function theorem; Lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- Let `f : E → F` between real Banach spaces be `C^∞` on `ball 0 ε` with `f 0 = 0` and surjective
derivative at `0`, and suppose `ker Df(0)` injects into a finite-dimensional space `K` through a
linear map `π₀`. Then every `k ∈ ker Df(0)` is the velocity at `0` of a `C^∞` curve of zeros of `f`
through `0` that stays in `ball 0 ε`. -/
theorem exists_contDiffOn_curve_of_fderiv_surjective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (ε : ℝ) (hε : 0 < ε) (hf : ContDiffOn ℝ ∞ f (ball 0 ε)) (hf0 : f 0 = 0)
    (hsurj : Function.Surjective (fderiv ℝ f 0))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K] (π₀ : E →ₗ[ℝ] K)
    (hker : ∀ x, fderiv ℝ f 0 x = 0 → π₀ x = 0 → x = 0)
    (k : E) (hk : fderiv ℝ f 0 k = 0) :
    ∃ r > 0, ∃ γ : ℝ → E, ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) ∧ γ 0 = 0 ∧ HasDerivAt γ k 0 ∧
      ∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε ∧ f (γ t) = 0 := by
  sorry

end FiniteEnergyPlane
