-- Prove2me | Theorems.Thm_FiniteEnergyPlane_two_le_windInf_of_negative_puncture
-- name    : FiniteEnergyPlane.two_le_windInf_of_negative_puncture
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:24:33.730027+00:00
-- url     : https://prove2.me/theorems/6f2de4d6-e5ea-4647-9bbf-01ba1c128a8d
-- title:
--   Negative punctures at orbits of index at least three have $\mathrm{wind}_\infty\ge2$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $\Gamma\subset\mathbb{C}$ be finite and $u$ a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ with $\int_{\mathbb{C}\setminus\Gamma}u^*d\lambda>0$. Let $z_0\in\Gamma$ be a negative puncture, nondegenerate in the sense of Hryniewicz, Definition 2.9, with asymptotic limit $Q$, where $Q$ is a nondegenerate orbit with $\mu_{CZ}(Q)\ge3$. Then $\mathrm{wind}_\infty(u,z_0)$ is defined and at least $2$.
--
--   **Formalization Note** The puncture is `IsNondegenerateEnd H u (cylEndAt z₀) Q (-1)`; the conclusion is `HasWindInfAt H u (cylEndAt z₀) (-1) k` with `2 ≤ k`, windings in the global frame of `FiniteEnergyPlane_Winding`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.13

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.13. Let `u` be a finite-energy `J̃`-holomorphic curve on
`ℂ \ Γ` (`Γ` finite) in the symplectization of `S ⊂ ℝ⁴` with positive `dλ`-energy, and let
`z₀ ∈ Γ` be a negative puncture, nondegenerate in the sense of Definition 2.9, whose asymptotic
limit `Q` is a nondegenerate orbit of Conley–Zehnder index at least `3`. Then `wind_∞(u, z₀) ≥ 2`
in the global frame. -/
theorem two_le_windInf_of_negative_puncture (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (z₀ : ℂ) (hz₀ : z₀ ∈ Γ)
    (Q : ReebOrbit H) (hend : IsNondegenerateEnd H u (cylEndAt z₀) Q (-1))
    (hQ : Q.IsNondegenerate) (hcz : Q.IsCZAtLeast 3) (hpos : dlambdaEnergy H (↑Γ)ᶜ u ≠ 0) :
    ∃ k : ℤ, HasWindInfAt H u (cylEndAt z₀) (-1) k ∧ 2 ≤ k := by
  sorry

end FiniteEnergyPlane
