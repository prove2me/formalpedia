-- Prove2me | Theorems.Thm_FiniteEnergyPlane_windInf_bounds_of_plane
-- name    : FiniteEnergyPlane.windInf_bounds_of_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T15:40:36.352657+00:00
-- url     : https://prove2.me/theorems/c0872264-50e5-4560-83ff-7ddaef974601
-- title:
--   Winding bounds for finite-energy planes at nondegenerate orbits
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic orbit of $X_{H_0}$ on $H_0^{-1}(1)$ and $Q$ a nondegenerate periodic Reeb orbit of $H$ with the same image and with period equal to the action $\int_0^{T_P}\lambda_0(\dot x)$ of $P$. Let $u$ be a finite-energy $\tilde J$-holomorphic plane whose puncture $\infty$ is nondegenerate (Hryniewicz, Definition 2.9) with asymptotic limit $Q$. Then $\mathrm{wind}_\infty(u)=k$ and $\mathrm{wind}_\pi(u)=k-1$ for an integer $k$ with
--   $$1\le k\le\Big\lfloor\frac{\mu_{CZ}(P)}{2}\Big\rfloor.$$
--
--   **Formalization Note** The orbits correspond as in `isNondegenerate_bridge` of the previous mission (transport by `Fin.cast`); the Conley–Zehnder index is `HryniewiczCriterion.czIndexOfPath (linearizedXiPath H₀ P Y)`, for every `Y` with `IsLinearizedFlow H₀ P.x Y`. The end is `IsNondegenerateEnd H u cylInf Q 1`; the conclusion is `HasWindInfAt H u cylInf 1 k ∧ HasWindPi H u ∅ (k - 1) ∧ 1 ≤ k` and `2 * k ≤ czIndexOfPath …` for every `Y`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Sections 3–4; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder; Hryniewicz (Trans. AMS 2012), §§ 3–4: let `u` be a finite-energy
`J̃`-holomorphic plane in the symplectization of `S ⊂ ℝ⁴` whose puncture `∞` is nondegenerate
(Definition 2.9) with a nondegenerate asymptotic limit `Q`, and let `P` be the corresponding
periodic orbit in `HryniewiczCriterion` (same image and action, as in `isNondegenerate_bridge`).
Then `wind_∞(u) = k` with `1 ≤ k ≤ ⌊μ_CZ(P) / 2⌋`, and `wind_π(u) = k - 1`. -/
theorem windInf_bounds_of_plane (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∀ u : ℂ → V 1, IsFiniteEnergyCurve H J Set.univ u → IsNondegenerateEnd H u cylInf Q 1 →
      ∃ k : ℤ, HasWindInfAt H u cylInf 1 k ∧ HasWindPi H u ∅ (k - 1) ∧ 1 ≤ k ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          2 * k ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) := by
  sorry

end FiniteEnergyPlane
