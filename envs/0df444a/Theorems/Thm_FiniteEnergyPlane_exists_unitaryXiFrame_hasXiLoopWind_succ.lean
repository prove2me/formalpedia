-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame_hasXiLoopWind_succ
-- name    : FiniteEnergyPlane.exists_unitaryXiFrame_hasXiLoopWind_succ
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T16:08:40.277521+00:00
-- url     : https://prove2.me/theorems/53159d78-0061-447f-82c0-695ed0e09dc3
-- title:
--   A unitary frame of the contact structure of winding one along a Reeb orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$ be a strictly star-shaped level, $\xi$ its contact structure with a compatible complex structure $J$, and $P=(x,T)$ a periodic Reeb orbit on $S$.
--
--   There is a unitary frame $M(t):\mathbb R^2\to\xi_{x(Tt)}$ of $\xi$ along $P$ (smooth, $1$-periodic, onto $\xi_{x(Tt)}$, $J$-complex linear for $J_0$ and symplectic-unitary) of winding one: for every continuous $1$-periodic nowhere-vanishing loop $\zeta$ in $\mathbb R^2\cong\mathbb C$ and every integer $k$, the loop $t\mapsto M(t)\zeta(t)$ has winding number $k+1$ in the global frame of $\xi$ if and only if $\zeta$ has winding number $k$.
--
--   This provides a frame of winding one along any orbit, as used for the normal frame of a fast finite-energy plane at its asymptotic orbit.
--
--   Formalization Note: the frame is `IsUnitaryXiFrame J P M`; windings are `HasXiLoopWind P` (global frame of $\xi$) and `HasLoopWind` of `vecToC ∘ ζ`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), proof of Lemma 6.10

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Along every periodic Reeb orbit `P` there is a unitary frame `M` of `ξ` of winding one: a
continuous `1`-periodic nowhere-vanishing loop `ζ` in `ℝ² = ℂ` has winding `k` iff the loop
`t ↦ M(t) ζ(t)` has winding `k + 1` in the global frame of `ξ`. -/
theorem exists_unitaryXiFrame_hasXiLoopWind_succ (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P M ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k) := by
  sorry

end FiniteEnergyPlane
