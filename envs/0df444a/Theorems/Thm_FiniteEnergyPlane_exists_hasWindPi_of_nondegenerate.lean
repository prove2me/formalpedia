-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasWindPi_of_nondegenerate
-- name    : FiniteEnergyPlane.exists_hasWindPi_of_nondegenerate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:38:37.173917+00:00
-- url     : https://prove2.me/theorems/c23a695b-17c8-498e-b4a3-98154025a234
-- title:
--   $\mathrm{wind}_\pi$ is defined and nonnegative
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $\Gamma\subset\mathbb{C}$ be finite and $u$ a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ such that $\infty$ is a positive puncture and every $z\in\Gamma$ a negative puncture, all nondegenerate in the sense of Hryniewicz, Definition 2.9, and suppose $\pi\,du$ does not vanish identically. Then every zero of $\pi\partial_su$ in $\mathbb{C}\setminus\Gamma$ is isolated and has local index at least $1$, there are finitely many, and $\mathrm{wind}_\pi(u)$ is defined and $\ge0$.
--
--   **Formalization Note** The punctures are `IsNondegenerateEnd H u cylInf P∞ 1` and `IsNondegenerateEnd H u (cylEndAt z) P_z (-1)` for $z\in\Gamma$; \"$\pi\,du\not\equiv0$\" is `∃ z ∉ Γ, piDs H u z ≠ 0`. The conclusion is `HasZeroIndex (piDs H u) z m` with `1 ≤ m` at every zero, and `HasWindPi H u Γ k` with `0 ≤ k`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4, formula (14)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, § 2.2.4 (14): let `u` be a finite-energy `J̃`-holomorphic curve on `ℂ \ Γ`, `Γ`
finite, whose puncture `∞` is positive and whose punctures in `Γ` are negative, all nondegenerate in
the sense of Definition 2.9, and suppose `π du` does not vanish identically. Then the zeros of
`π ∂ₛu` in `ℂ \ Γ` are isolated, each has local index at least `1`, and there are finitely many,
so `wind_π(u)` is defined and nonnegative. -/
theorem exists_hasWindPi_of_nondegenerate (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    (∀ z ∉ Γ, piDs H u z = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z m) ∧
      ∃ k : ℤ, 0 ≤ k ∧ HasWindPi H u Γ k := by
  sorry

end FiniteEnergyPlane
