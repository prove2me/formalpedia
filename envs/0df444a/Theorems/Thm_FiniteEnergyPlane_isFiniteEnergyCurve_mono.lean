-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_mono
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_mono
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T19:50:28.509976+00:00
-- url     : https://prove2.me/theorems/00b32bf9-3ed6-44e4-bc1d-4c5812f6c6d3
-- title:
--   Restriction of a finite-energy curve to a subdomain
-- statement:
--   Let $S=H^{-1}(1)$ be a level in $\mathbb{R}^{2n+2}$, $J$ a complex structure on $\xi$, and $u$ a finite-energy $\tilde J$-holomorphic curve on $U\subseteq\mathbb{C}$. If $W\subseteq U$, then $u$ is a finite-energy $\tilde J$-holomorphic curve on $W$, and
--   $$E(u;W)\le E(u;U),\qquad \int_W u^*d\lambda\le\int_U u^*d\lambda .$$
--
--   **Formalization Note** Here $\int_W u^*d\lambda$ is `dlambdaEnergy`, the integral over $W$ of the positive part of $\omega_0(\partial_s w,\partial_t w)$ with $w=\mathrm{proj}\circ u$; $W$ need not be open.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 4 (supporting lemma for Lemma 4.16)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The restriction of a finite-energy curve on `U` to a subset `W ⊆ U` is a finite-energy curve
on `W`, with Hofer energy and `dλ`-energy on `W` at most those on `U`. -/
theorem isFiniteEnergyCurve_mono {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (U W : Set ℂ)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (hWU : W ⊆ U) :
    IsFiniteEnergyCurve H J W u ∧ energy H W u ≤ energy H U u ∧
      dlambdaEnergy H W u ≤ dlambdaEnergy H U u := by
  sorry

end FiniteEnergyPlane
