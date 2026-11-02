-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_of_hasAsymptoticEigenvector
-- name    : FiniteEnergyPlane.exists_hasWindInfAt_of_hasAsymptoticEigenvector
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:38:49.366667+00:00
-- url     : https://prove2.me/theorems/afb7a8c8-d1a7-420b-9c7f-21473d717960
-- title:
--   $\mathrm{wind}_\infty$ is the winding of the asymptotic eigenvector
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $u$ be a finite-energy $\tilde J$-holomorphic curve on a punctured disk $B_r(z_0)\setminus\{z_0\}$, and suppose that at $z_0$, with sign $\varepsilon=\pm1$, $u$ has an asymptotic eigenvalue $\mu$ and asymptotic eigenvector $v$ of $A_P$ for a periodic Reeb orbit $P$ (Hryniewicz, Theorem 2.11). Then $\mathrm{wind}_\infty$ of $u$ at $z_0$ is defined and equals the winding number of $v$ in the global frame.
--
--   **Formalization Note** The hypothesis is `HasAsymptoticEigenvector H J u (cylEndAt z₀) P ε μ v` of `FiniteEnergyPlane_Asymptotics`; the conclusion is `∃ k, HasXiLoopWind P v k ∧ HasWindInfAt H u (cylEndAt z₀) ε k`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.16 and Remark 2.17; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.8

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Lemma 2.16 and Remark 2.17; Hryniewicz (Trans. AMS 2012), Lemma 6.8: at a puncture
`z₀` of sign `ε` where `u` has an asymptotic eigenvector `v` (Theorem 2.11), the asymptotic
winding `wind_∞` of `u` at `z₀` is defined and equals the winding number of `v` in the global
frame. -/
theorem exists_hasWindInfAt_of_hasAsymptoticEigenvector (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (ball z₀ r \ {z₀}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) (v : ℝ → V 1)
    (hv : HasAsymptoticEigenvector H J u (cylEndAt z₀) P ε μ v) :
    ∃ k : ℤ, HasXiLoopWind P v k ∧ HasWindInfAt H u (cylEndAt z₀) ε k := by
  sorry

end FiniteEnergyPlane
