-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_eq_zero_or_isolated
-- name    : FiniteEnergyPlane.exists_ball_piDs_eq_zero_or_isolated
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-02T20:29:22.930556+00:00
-- url     : https://prove2.me/theorems/6eae9220-bbba-432c-891d-324379097a71
-- title:
--   Zeros of $\pi\,\partial_s u$ are isolated with positive index or fill a disc
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $U\subseteq\mathbb{C}$ be open and $u:U\to\mathbb{R}^4\setminus\{0\}$ a smooth $\tilde J$-holomorphic map, and write $\Pi(z)$ for $\pi\,\partial_s(\mathrm{pr}\circ u)(z)$ expressed in the global frame of $\xi$. Then every $z_0\in U$ has a disc $B(z_0,r)\subseteq U$ on which one of the following holds:
--
--   1. $\Pi\equiv0$ on $B(z_0,r)$; or
--   2. $\Pi$ has no zero in $B(z_0,r)\setminus\{z_0\}$, and if $\Pi(z_0)=0$ then $z_0$ is a zero of $\Pi$ of local index $m\ge1$.
--
--   This is the local statement behind Hryniewicz's definition (14) of $\mathrm{wind}_\pi$: zeros of $\pi\,du$ are either isolated with positive local index or fill an open set.
--
--   **Formalization Note** The map is given by `ContDiffOn ℝ ∞ u U`, `u z ≠ 0` on `U` and `JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u`; $\Pi$ is `piDs H u`, and "zero of local index $m$" is `HasZeroIndex (piDs H u) z₀ m` from `FiniteEnergyPlane_Winding`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4, discussion of formula (14) (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Local structure of the zeros of `π ∂ₛu`: let `u` be a smooth `J̃`-holomorphic map into
`V 1 \ {0}` on an open set `U ⊆ ℂ` and `z₀ ∈ U`. Then on some disc `B(z₀, r) ⊆ U` either `π ∂ₛu`
vanishes identically, or `π ∂ₛu` has no zero in `B(z₀, r) \ {z₀}` and, if `z₀` is a zero, it is
a zero of local index at least `1`. -/
theorem exists_ball_piDs_eq_zero_or_isolated (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U : Set ℂ) (hU : IsOpen U) (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U)
    (hu0 : ∀ z ∈ U, u z ≠ 0) (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ r > (0 : ℝ), ball z₀ r ⊆ U ∧
      ((∀ z ∈ ball z₀ r, piDs H u z = 0) ∨
        ((∀ z ∈ ball z₀ r, z ≠ z₀ → piDs H u z ≠ 0) ∧
          (piDs H u z₀ = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z₀ m))) := by
  sorry

end FiniteEnergyPlane
