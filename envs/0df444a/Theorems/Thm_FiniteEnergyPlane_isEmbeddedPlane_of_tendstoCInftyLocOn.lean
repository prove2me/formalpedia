-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isEmbeddedPlane_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.isEmbeddedPlane_of_tendstoCInftyLocOn
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:11:02.256819+00:00
-- url     : https://prove2.me/theorems/345d19ee-a81e-4df8-8816-5ea6443c9690
-- title:
--   $C^\infty_{loc}$ limits of embedded fast planes are embedded
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u_k$ be embedded fast finite-energy planes which converge in $C^\infty_{loc}(\mathbb{C})$ to a fast finite-energy plane $v$. Then $v$ is embedded.
--
--   **Formalization Note** "Fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`, and $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `Set.univ`. No hypothesis on the asymptotic orbits of $u_k$ and $v$ is made; they need not coincide.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 4.7 (closedness of $\Lambda(H,P)$ in $\Theta(H,P)$)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 4.7 (closedness of `Λ`). Let `uₖ` be embedded fast
finite-energy planes converging in `C^∞_loc(ℂ)` to a fast finite-energy plane `v`. Then `v` is
embedded. -/
theorem isEmbeddedPlane_of_tendstoCInftyLocOn (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℕ → ℂ → V 1) (v : ℂ → V 1) (hu : ∀ k, IsFastPlane H J (u k))
    (hue : ∀ k, IsEmbeddedPlane (u k)) (hv : IsFastPlane H J v)
    (hconv : JHolomorphic.TendstoCInftyLocOn u v Set.univ) :
    IsEmbeddedPlane v := by
  sorry

end FiniteEnergyPlane
