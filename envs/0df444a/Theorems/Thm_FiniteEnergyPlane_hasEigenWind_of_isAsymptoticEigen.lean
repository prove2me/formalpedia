-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasEigenWind_of_isAsymptoticEigen
-- name    : FiniteEnergyPlane.hasEigenWind_of_isAsymptoticEigen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T10:42:43.759711+00:00
-- url     : https://prove2.me/theorems/9fe6808f-a32e-41f3-9bd3-7268400d579b
-- title:
--   One eigenvector's winding determines the eigenvalue's winding
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with contact structure $\xi$, let $J$ be a $d\lambda_0$-compatible complex structure on $\xi$, and let $P=(x,T)$ be a periodic Reeb orbit on $S$ (not necessarily nondegenerate) with asymptotic operator $A_P$. If $v$ is an eigenvector of $A_P$ with eigenvalue $\mu$ whose winding number in Hryniewicz's global frame of $\xi$ is $k$, then $\mu$ has eigenvector winding $k$: every eigenvector of $A_P$ with eigenvalue $\mu$ has winding number $k$ in the global frame.
--
--   So the winding of a single eigenvector determines the winding attached to its eigenvalue. This is what is needed to compare the asymptotic winding $\mathrm{wind}_\infty$ of a finite-energy curve with the numbers $\alpha^\pm(P)$.
--
--   **Formalization Note** "$v$ is an eigenvector with eigenvalue $\mu$" is `IsAsymptoticEigen J P μ v`; its winding in the global frame is `HasXiLoopWind P v k`; the conclusion `HasEigenWind J P μ k` says that some eigenvector for $\mu$ exists and every one has winding $k$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4; C. Wendl, Lectures on Symplectic Field Theory, Theorem 3.7.1 (after Hofer-Wysocki-Zehnder)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If one eigenvector `v` of the asymptotic operator `A_P` with eigenvalue `μ` has winding `k` in
the global frame of `ξ`, then every eigenvector of `A_P` with eigenvalue `μ` has winding `k`. -/
theorem hasEigenWind_of_isAsymptoticEigen (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (μ : ℝ) (v : ℝ → V 1) (k : ℤ) (hv : IsAsymptoticEigen J P μ v) (hk : HasXiLoopWind P v k) :
    HasEigenWind J P μ k := by
  sorry

end FiniteEnergyPlane
