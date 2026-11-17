-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopEigenWind_of_comp_add
-- name    : FiniteEnergyPlane.hasLoopEigenWind_of_comp_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:23:47.413864+00:00
-- url     : https://prove2.me/theorems/752eb535-06b9-4cc8-97bc-aa014071d81d
-- title:
--   Windings of loop eigenfunctions are invariant under a shift of the loop
-- statement:
--   Let $S_\infty : \mathbb{R} \to \mathbb{R}^{2\times 2}$ be a loop of real $2 \times 2$ matrices, $c, \mu \in \mathbb{R}$ and $k \in \mathbb{Z}$. If $\mu$ is an eigenvalue of $-J_0 \partial_t - S_\infty(\cdot + c)$ on $1$-periodic loops and every eigenfunction for $\mu$ has winding number $k$, then $\mu$ is an eigenvalue of $-J_0 \partial_t - S_\infty$ and every eigenfunction for $\mu$ has winding number $k$.
--
--   Role: lets winding conditions on an asymptotic operator be transferred to the operator of a rotated (time-shifted) end.
--
--   Formalization Note: the hypothesis and conclusion are `HasLoopEigenWind (fun t => Sinf (t + c)) μ k` and `HasLoopEigenWind Sinf μ k`.
-- source:
--   Standard; asymptotic operators and windings as in H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Windings of loop eigenfunctions are unchanged by a shift of the loop: if `S∞(· + c)` has
eigenvalue `μ` of winding `k`, then so does `S∞`. -/
theorem hasLoopEigenWind_of_comp_add (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (c μ : ℝ) (k : ℤ)
    (h : HasLoopEigenWind (fun t => Sinf (t + c)) μ k) : HasLoopEigenWind Sinf μ k := by
  sorry

end FiniteEnergyPlane
