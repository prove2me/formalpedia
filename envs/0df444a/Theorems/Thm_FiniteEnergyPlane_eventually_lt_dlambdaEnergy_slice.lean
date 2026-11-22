-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eventually_lt_dlambdaEnergy_slice
-- name    : FiniteEnergyPlane.eventually_lt_dlambdaEnergy_slice
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:35:54.492836+00:00
-- url     : https://prove2.me/theorems/c4022c0c-3237-463b-b9aa-5a2a30ae6cfe
-- title:
--   Lower semicontinuity of the dλ-energy of the slices of a C^1 family
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be strictly star-shaped, $I\subseteq\mathbb{R}$ open, $U$ of class $C^1$ on $I\times\mathbb{C}$ with $U\neq0$ there, $t_0\in I$, $\tau_k\in I$ with $\tau_k\to t_0$, and $s\subseteq\mathbb{C}$. If $x<\int_s U(t_0,\cdot)^*d\lambda$, then $x<\int_s U(\tau_k,\cdot)^*d\lambda$ for all large $k$.
--
--   The $d\lambda$-energy on a fixed set is lower semicontinuous along a $C^1$ family of maps. It is used to compare the energy distribution of nearby leaves of a family of planes (Hryniewicz 2012, Lemma 7.2).
--
--   **Formalization Note** The $d\lambda$-energy is `dlambdaEnergy H s u = ∫⁻ z in s, ENNReal.ofReal (dlambdaDensity H u z)` (values in $[0,\infty]$; only the positive part of the density counts), where the density is $\omega_0(\partial_s w,\partial_t w)$ for $w=\mathrm{pr}_S\circ u$. No measurability of $s$ is assumed.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `U` be `C¹` and nonvanishing on `I × ℂ` (`I` open), `t₀ ∈ I`, `τ k ∈ I` with
`τ k → t₀`, and `s ⊆ ℂ`. If `x` is less than the `dλ`-energy of `U(t₀, ·)` on `s`, then `x` is
eventually less than the `dλ`-energy of `U(τ k, ·)` on `s`. -/
theorem eventually_lt_dlambdaEnergy_slice (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (U : ℝ × ℂ → V 1) (I : Set ℝ) (hI : IsOpen I) (hU : ContDiffOn ℝ 1 U (I ×ˢ Set.univ))
    (hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0) (t₀ : ℝ) (ht₀ : t₀ ∈ I)
    (τ : ℕ → ℝ) (hτI : ∀ k, τ k ∈ I) (hτ : Tendsto τ atTop (𝓝 t₀)) (s : Set ℂ)
    (x : ℝ≥0∞) (hx : x < dlambdaEnergy H s (fun z => U (t₀, z))) :
    ∀ᶠ k in atTop, x < dlambdaEnergy H s (fun z => U (τ k, z)) := by
  sorry

end FiniteEnergyPlane
