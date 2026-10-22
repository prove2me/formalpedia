-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaDensity_pos_eventually
-- name    : FiniteEnergyPlane.dlambdaDensity_pos_eventually
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:43:41.892291+00:00
-- url     : https://prove2.me/theorems/832b01cb-0797-4acb-8715-2e227f10b870
-- title:
--   The transverse derivative has no zeros near a nondegenerate puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, and suppose $0$ is a nondegenerate puncture of $u$, asymptotic to a periodic Reeb orbit $P$ with sign $\varepsilon=\pm1$. If $\pi\,du$ does not vanish identically on any punctured neighbourhood of $0$, then there is $r>0$ such that $\pi\,du(z)\neq0$, equivalently $\omega_0(\partial_sw,\partial_tw)(z)>0$, for all $0<|z|<r$.
--
--   **Formalization Note** $\omega_0(\partial_sw,\partial_tw)$ with $w=\mathrm{proj}\circ u$ is `dlambdaDensity H u z`, in the coordinate $z=s+it$ of the disk. The hypothesis is that every punctured disk $B_r(0)\setminus\{0\}$ contains a point where it is nonzero. $P$ need not be nondegenerate.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.9 (3); U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Definition 3.11 (3)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Definition 2.9 (3): for a finite-energy `J̃`-holomorphic curve on `D \ {0}` with a
nondegenerate puncture at `0`, if `π du` does not vanish identically near `0`, then `π du` has no
zeros near `0`, i.e. `ω₀(∂ₛw, ∂ₜw) > 0` on a punctured neighborhood of `0`. -/
theorem dlambdaDensity_pos_eventually {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylEnd P ε)
    (hπ : ∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H u z ≠ 0) :
    ∃ r > 0, ∀ z ∈ ball (0 : ℂ) r \ {0}, 0 < dlambdaDensity H u z := by
  sorry

end FiniteEnergyPlane
