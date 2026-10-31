-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_zero
-- name    : FiniteEnergyPlane.isAsymptoticEigen_apply_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T16:37:06.274643+00:00
-- url     : https://prove2.me/theorems/448bc0b2-bc43-4422-8045-4e9738764eb7
-- title:
--   Eigenvectors of the asymptotic operator vanish nowhere
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit on $S$ (not assumed nondegenerate). Let $v:\mathbb{R}\to\mathbb{R}^{2n+2}$ be a smooth $1$-periodic loop with $v(t)\in\xi_{x(Tt)}$ for all $t$, not identically zero, and with $A_Pv=\mu v$ for some $\mu\in\mathbb{R}$, where $A_P\eta(t)=J(x(Tt))\big(-\eta'(t)+T\,DR(x(Tt))\,\eta(t)\big)$ is the asymptotic operator of $P$. Then $v(t)\neq0$ for every $t\in\mathbb{R}$.
--
--   This is used to show that the leading term of an asymptotic expansion of a pseudoholomorphic half-cylinder at a puncture vanishes nowhere.
--
--   **Formalization Note** The hypothesis is `IsAsymptoticEigen J P μ v` (defined in `FiniteEnergyPlane_Asymptotics`), with `asympOp` the operator $A_P$.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270-328, Section 3; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- An eigenvector of the asymptotic operator `A_P` of a periodic Reeb orbit vanishes nowhere:
if `A_P v = μ v` for a `ξ`-loop `v` that is not identically zero, then `v(t) ≠ 0` for every `t`. -/
theorem isAsymptoticEigen_apply_ne_zero {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (μ : ℝ)
    (v : ℝ → V n) (hv : IsAsymptoticEigen J P μ v) (t : ℝ) : v t ≠ 0 := by
  sorry

end FiniteEnergyPlane
