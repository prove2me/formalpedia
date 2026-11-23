-- Prove2me | Theorems.Thm_FiniteEnergyPlane_snd_eq_of_fderiv_eq_radial
-- name    : FiniteEnergyPlane.snd_eq_of_fderiv_eq_radial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:28:52.003219+00:00
-- url     : https://prove2.me/theorems/703d14c0-90d1-4f89-a7f4-b31e70513f8b
-- title:
--   The parameter component of the pulled-back radial field is constant along the leaves of a family of fast planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be strictly star-shaped, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$, and $f:\mathbb{C}\times B_r(0)\to\mathbb{R}^4$ a $C^1$ injective map with injective derivative such that every $f(\cdot,\tau)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Let $|\tau|<r$ and $w,w'\in\mathbb{C}$. If $\Delta,\Delta'\in\mathbb{C}\times\mathbb{C}$ satisfy
--   $$Df(w,\tau)\Delta=f(w,\tau),\qquad Df(w',\tau)\Delta'=f(w',\tau),$$
--   then the $\tau$-components of $\Delta$ and $\Delta'$ agree.
--
--   The radial field $y$ on $\mathbb{R}^4\setminus\{0\}$, which generates the $\mathbb{R}$-translations of the symplectization, pulls back under $f$ to a field whose parameter component depends on the leaf only. It is used for the immersion property of the projected family (Hryniewicz 2012, Lemma 7.3).
--
--   **Formalization Note** The embedded fast planes are given by `IsFastPlane`, `IsNondegenerateEnd … cylInf P 1` and `IsEmbeddedPlane`; the index condition is `P.IsCZAtLeast 3`; the parameter component is `Prod.snd`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` have Conley–Zehnder index at least `3` and let `f : ℂ × B_r(0) → V 1` be `C¹`,
injective, with injective derivative, such that every `f(·, τ)` is an embedded fast finite-energy
plane asymptotic to `P` at `∞`. If `Df(w, τ) Δ = f(w, τ)` and `Df(w', τ) Δ' = f(w', τ)`, then `Δ` and
`Δ'` have the same parameter component. -/
theorem snd_eq_of_fderiv_eq_radial (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (r : ℝ) (f : ℂ × ℂ → V 1)
    (hf : ContDiffOn ℝ 1 f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hfinj : Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r))
    (hdf : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p))
    (hslice : ∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
      IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ)))
    (τ : ℂ) (hτ : τ ∈ ball (0 : ℂ) r) (w w' : ℂ) (Δ Δ' : ℂ × ℂ)
    (hΔ : fderiv ℝ f (w, τ) Δ = f (w, τ)) (hΔ' : fderiv ℝ f (w', τ) Δ' = f (w', τ)) :
    Δ.2 = Δ'.2 := by
  sorry

end FiniteEnergyPlane
