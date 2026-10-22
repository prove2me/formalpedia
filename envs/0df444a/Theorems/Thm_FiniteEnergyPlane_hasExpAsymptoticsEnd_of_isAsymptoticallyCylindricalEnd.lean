-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd
-- name    : FiniteEnergyPlane.hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:43:16.0682+00:00
-- url     : https://prove2.me/theorems/df52d1da-c6a8-4ddb-a717-92281bbcbde0
-- title:
--   Asymptotically cylindrical ends at nondegenerate orbits converge exponentially
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a nondegenerate periodic Reeb orbit and $\varepsilon=\pm1$. If $u$ is asymptotically cylindrical over $P$ with sign $\varepsilon$ in the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$, then there is $b>0$ such that $u$ has exponential asymptotics with rate $b$ there: for some $d,c$, both $a(s,t)-\varepsilon Ts-d$ and $w(s,t)-x(\varepsilon Tt+c)$ decay like $e^{-bs}$ with all derivatives.
--
--   **Formalization Note** The conclusion is `∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b`, which contains the conditions of `IsNondegenerateEnd`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy `J̃`-holomorphic curve on `D \ {0}` that is asymptotically cylindrical over a
nondegenerate periodic Reeb orbit `P` at the puncture converges to the trivial cylinder over `P`
exponentially fast in `C^∞`, for some rate `b > 0`. In particular the puncture satisfies
Hryniewicz, Definition 2.9 (1), (2), (4). -/
theorem hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hac : IsAsymptoticallyCylindricalEnd H u cylEnd P ε) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b := by
  sorry

end FiniteEnergyPlane
