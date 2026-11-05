-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebOrbit_loop_of_cylinder
-- name    : FiniteEnergyPlane.exists_reebOrbit_loop_of_cylinder
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:16:12.38121+00:00
-- url     : https://prove2.me/theorems/da7803f4-f012-4e68-aedc-1a40a0e1fb1d
-- title:
--   The unit loop of a finite-energy cylinder of small area with positive actions is a periodic orbit
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level. Let $C,e,\eta$ with $e,\eta>0$, where $e$ is smaller than the difference of any two distinct periods at most $C$ of periodic Reeb orbits. Let $w$ be a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\{0\}$ with Hofer energy at most $C$, $d\lambda$-energy at most $e$, and action at least $\eta$ on every counterclockwise circle about $0$. Then there are a periodic Reeb orbit $(x,T)$ with $T\le C$ and $c\in\mathbb{R}$ such that $\mathrm{proj}(w(e^{2\pi it}))=x(Tt+c)$ for all $t$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Finite-energy cylinders of small area. Let `e, η > 0`, with `e` smaller than the difference of
any two distinct periods at most `C` of periodic Reeb orbits, and let `w` be a finite-energy
`J̃`-holomorphic curve on `ℂ \ {0}` with Hofer energy at most `C`, `dλ`-energy at most `e` and action
at least `η` on every counterclockwise circle about `0`. Then there are a periodic Reeb orbit `(x, T)`
with `T ≤ C` and `c ∈ ℝ` with `proj(w(e^{2π i t})) = x(T t + c)` for all `t`. -/
theorem exists_reebOrbit_loop_of_cylinder {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (w : ℂ → V n)
    (hw : IsFiniteEnergyCurve H J {z | z ≠ 0} w) (C e η : ℝ) (he : 0 < e)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (hE : energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C)
    (hd : dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e)
    (hact : ∀ ρ : ℝ, 0 < ρ → η ≤ loopAction H w (ccwLoop ρ)) :
    ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ t : ℝ,
      loopInS H w (ccwLoop 1) t = Q.x (Q.T * t + c) := by
  sorry

end FiniteEnergyPlane
