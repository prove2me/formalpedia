-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_expDecay_of_isAsymptoticallyCylindricalEnd
-- name    : FiniteEnergyPlane.exists_expDecay_of_isAsymptoticallyCylindricalEnd
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-29T20:20:21.88579+00:00
-- url     : https://prove2.me/theorems/5dd407d1-f1ef-422d-8fdf-ed93d18aa14c
-- title:
--   Exponential $C^0$ convergence of asymptotically cylindrical ends at nondegenerate orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a nondegenerate periodic Reeb orbit and $\varepsilon=\pm1$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ write $a(s,t)$ for the symplectization coordinate and $w(s,t)\in S$ for the projection of $u$. Suppose that for some constants $d,c$ both $a(s,t)-\varepsilon Ts-d$ and $w(s,t)-x(\varepsilon Tt+c)$ tend to $0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. Then there are $\delta>0$, $C$ and $s_0$ such that for all $s\ge s_0$ and all $t$,
--   $$|a(s,t)-\varepsilon Ts-d|\le Ce^{-\delta s},\qquad \|w(s,t)-x(\varepsilon Tt+c)\|\le Ce^{-\delta s}.$$
--
--   This is the $C^0$ part of the exponential convergence of nondegenerate ends (Hryniewicz, Theorem 2.10), with the same constants $d,c$ as in the hypothesis.
--
--   **Formalization Note** The hypotheses are the two `TendstoZeroCInfty` conditions of `IsAsymptoticallyCylindricalEnd H u cylEnd P ε` with the constants $d,c$ made explicit; $a$ and $w$ are `endA H u cylEnd` and `endW H u cylEnd`, and the norm on $V$ is the sup norm.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996); C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}` that is asymptotically
cylindrical over a nondegenerate periodic Reeb orbit `P` with sign `ε`, with constants `d, c`, in
the cylindrical coordinates `cylEnd` at the puncture. Then both `a(s, t) - εTs - d` and
`w(s, t) - x(εTt + c)` decay like `e^{-δs}` uniformly in `t`, for some `δ > 0`. -/
theorem exists_expDecay_of_isAsymptoticallyCylindricalEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (d c : ℝ)
    (ha : TendstoZeroCInfty (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (ε * P.T * p.2 + c))) :
    ∃ δ > 0, ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      |endA H u cylEnd (s, t) - ε * P.T * s - d| ≤ C * Real.exp (-(δ * s)) ∧
        ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
