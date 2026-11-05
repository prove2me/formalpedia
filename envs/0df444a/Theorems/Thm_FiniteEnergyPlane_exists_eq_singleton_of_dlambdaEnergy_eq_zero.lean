-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_singleton_of_dlambdaEnergy_eq_zero
-- name    : FiniteEnergyPlane.exists_eq_singleton_of_dlambdaEnergy_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:34:10.987451+00:00
-- url     : https://prove2.me/theorems/0c262cf1-2098-4a91-b6a1-a60ba81fc826
-- title:
--   A finite-energy curve with one positive prime puncture, negative punctures and no $d\lambda$-energy is a trivial cylinder
-- statement:
--   Let $w$ be a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$, $\Gamma$ finite, in the symplectization of a strictly star-shaped level $S\subset\mathbb{R}^4$. Suppose $w$ has a nondegenerate positive puncture at $\infty$ over a prime periodic Reeb orbit $P=(x,T)$, the action of $w$ on circles of radius $\rho$ tends to $T$ as $\rho\to\infty$, the coordinate $a\circ w$ tends to $-\infty$ at every point of $\Gamma$, and $\int_{\mathbb{C}\setminus\Gamma}w^*d\lambda=0$. Then $\Gamma$ is a single point $z_1$; for every $z\ne z_1$ the projection of $w(z)$ to $S$ lies on the image of $x$ and $\pi\,\partial_s\mathrm{pr}(w)(z)=0$; and the action of $w$ on every circle $|z|=\rho>|z_1|$ equals $T$.
--
--   This identifies the $d\lambda$-energy-free limits that occur in the compactness theory of fast planes.
--
--   **Formalization Note** `IsNondegenerateEnd H w cylInf P 1`, `P.IsPrime`, `piDs H w z` and `loopAction H w (ccwLoop ρ)` are the published objects; the $d\lambda$-energy is `dlambdaEnergy H (↑Γ)ᶜ w`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `w` be a finite-energy `J̃`-holomorphic curve on `ℂ \ Γ`, `Γ` finite, in the symplectization of
`S ⊂ ℝ⁴`, with vanishing `dλ`-energy, `aCoord H ∘ w → -∞` at every point of `Γ`, and a nondegenerate
positive puncture at `∞` over a prime orbit `P` with `∫_{|z| = ρ} w*λ → P.T` as `ρ → ∞`. Then `Γ` is a
single point `z₁`, the projection of `w` lies in the image of `P`, `π ∂ₛw` vanishes identically, and
`∫_{|z| = ρ} w*λ = P.T` for every `ρ > ‖z₁‖`. -/
theorem exists_eq_singleton_of_dlambdaEnergy_eq_zero (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (P : ReebOrbit H) (hprime : P.IsPrime) (hinf : IsNondegenerateEnd H w cylInf P 1)
    (hact : Tendsto (fun ρ : ℝ => loopAction H w (ccwLoop ρ)) atTop (𝓝 P.T))
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => aCoord H (w z)) (𝓝[≠] z₀) atBot)
    (hzero : dlambdaEnergy H (↑Γ)ᶜ w = 0) :
    ∃ z₁ : ℂ, Γ = {z₁} ∧ (∀ z ∉ Γ, proj H (w z) ∈ Set.range P.x ∧ piDs H w z = 0) ∧
      ∀ ρ : ℝ, ‖z₁‖ < ρ → loopAction H w (ccwLoop ρ) = P.T := by
  sorry

end FiniteEnergyPlane
