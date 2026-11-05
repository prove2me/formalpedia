-- Prove2me | Theorems.Thm_FiniteEnergyPlane_loopAction_le_and_dlambdaEnergy_annulus_eq
-- name    : FiniteEnergyPlane.loopAction_le_and_dlambdaEnergy_annulus_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:24.917197+00:00
-- url     : https://prove2.me/theorems/3891cb83-f718-48b3-b5a9-6153ae6e4731
-- title:
--   The $d\lambda$-energy of an annulus is the difference of the boundary actions
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic curve on an open set $U\subset\mathbb{C}$ containing the closed annulus $a\le|z|\le b$, $0<a\le b$. Let $\mathcal{A}(\rho)$ be the action of the counterclockwise loop $t\mapsto \mathrm{proj}(u(\rho e^{2\pi it}))$. Then $\mathcal{A}(a)\le\mathcal{A}(b)$, and the $d\lambda$-energy of $u$ on $\{a\le|z|<b\}$ equals $\mathcal{A}(b)-\mathcal{A}(a)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The `dλ`-energy of an annulus. Let `u` be a finite-energy `J̃`-holomorphic curve on an open set
`U` containing the closed annulus `a ≤ |z| ≤ b`, `0 < a ≤ b`. Then the action of the counterclockwise
circle of radius `a` is at most that of radius `b`, and the `dλ`-energy of `u` on `{a ≤ |z| < b}` is
their difference. -/
theorem loopAction_le_and_dlambdaEnergy_annulus_eq {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) :
    loopAction H u (ccwLoop a) ≤ loopAction H u (ccwLoop b) ∧
      dlambdaEnergy H (ball 0 b \ ball 0 a) u =
        ENNReal.ofReal (loopAction H u (ccwLoop b) - loopAction H u (ccwLoop a)) := by
  sorry

end FiniteEnergyPlane
