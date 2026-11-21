-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:19:12.381587+00:00
-- url     : https://prove2.me/theorems/c1fefcf1-fbdb-4575-9fb0-da04c04f6bd8
-- title:
--   A fast plane has an asymptotic eigenvector of winding one at infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $P=(x,T)$ a periodic Reeb orbit, and $\tilde u:\mathbb{C}\to\mathbb{R}^4$ a fast finite-energy plane asymptotic to $P$ at $\infty$. Then, in the cylindrical coordinates $z=e^{2\pi(s+it)}$ at $\infty$, $\tilde u$ has an asymptotic eigenvalue $\mu$ with an asymptotic eigenvector $v$ of $A_P$ whose winding number in the global frame of $\xi$ is
--   $$\mathrm{wind}(v)=1 .$$
--
--   Role: the asymptotic formula of a fast plane at its positive puncture together with the winding of its leading eigenvector, as needed to compare two fast planes over the same orbit.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (Hryniewicz 2014, Definition 2.9; $P$ may be degenerate); the asymptotic formula is `HasAsymptoticEigenvector H J u cylInf P 1 μ v`, which includes $\mu<0$; winding is `HasXiLoopWind P v 1`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Definition 2.14 and Lemma 6.23; U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.11

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A fast finite-energy plane `u` with a nondegenerate end at `∞` asymptotic to `P` has, in the
cylindrical coordinates `cylInf`, an asymptotic eigenvalue `μ` with an asymptotic eigenvector `v`
of `A_P` whose winding number in the global frame of `ξ` is `1`. -/
theorem exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v ∧
      HasXiLoopWind P v 1 := by
  sorry

end FiniteEnergyPlane
