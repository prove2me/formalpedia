-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_one_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.hasWindInfAt_one_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:59:36.947806+00:00
-- url     : https://prove2.me/theorems/29aa8ca1-2cee-44ec-847d-33b12ca7dc49
-- title:
--   Limits of normalized fast planes have asymptotic winding one at $\infty$
-- statement:
--   Let $u_k$ be a sequence in the set $\Theta(K,P)$ of fast finite-energy planes asymptotic to a periodic Reeb orbit $P$ at $\infty$ on a strictly star-shaped level $S\subset\mathbb{R}^4$, with $u_k(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk. Suppose the radial rescalings of the $u_k$ normalized at the point $2$ converge in $C^\infty_{\mathrm{loc}}(\mathbb{C}\setminus\Gamma)$, with $\Gamma$ a finite subset of the closed unit disk, to a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\Gamma$ that has a nondegenerate positive puncture at $\infty$ over $P$ and nonzero $d\lambda$-energy. Then $\mathrm{wind}_\infty(w)=1$.
--
--   The fast condition on planes is thus inherited at $\infty$ by those limits that carry $d\lambda$-energy.
--
--   **Formalization Note** $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$ is `V 1 \ {0}`, with $a$ = `aCoord H` and $\mathrm{pr}$ = `proj H`; $\Theta$ = `fastPlaneSet H J P K γ`. The conclusion is `HasWindInfAt H w cylInf 1 1`; the rescaling is `(Real.exp (-(2 * a_k 2))) • u_k`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `uₖ` be a sequence in `fastPlaneSet H J P K γ` whose shifts `e^{-2aₖ(2)} • uₖ` converge in
`C^∞_loc(ℂ \ Γ)` to a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ Γ`, with `Γ` a finite subset of
the closed unit disk. If `w` has a nondegenerate positive puncture at `∞` over `P` and positive
`dλ`-energy, then `wind_∞(w, ∞) = 1` in the global frame. -/
theorem hasWindInfAt_one_of_tendstoCInftyLocOn (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ)
    (Γ : Finset ℂ) (hΓ : ∀ z ∈ Γ, ‖z‖ ≤ 1) (w : ℂ → V 1) (hw : IsFiniteEnergyCurve H J (↑Γ)ᶜ w)
    (hconv : JHolomorphic.TendstoCInftyLocOn
      (fun k z => Real.exp (-(2 * aCoord H (u k 2))) • u k z) w (↑Γ)ᶜ)
    (hinf : IsNondegenerateEnd H w cylInf P 1) (hpos : dlambdaEnergy H (↑Γ)ᶜ w ≠ 0) :
    HasWindInfAt H w cylInf 1 1 := by
  sorry

end FiniteEnergyPlane
