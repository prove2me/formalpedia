-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebOrbit_of_tendsto
-- name    : FiniteEnergyPlane.exists_reebOrbit_of_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T16:15:33.727339+00:00
-- url     : https://prove2.me/theorems/98b1d224-8a69-4c40-b83b-928d2f4b189e
-- title:
--   Limits of periodic Reeb orbits with converging initial points and periods
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $Q_k=(x_k,T_k)$ periodic Reeb orbits on $S$ with $x_k(0)\to p$ and $T_k\to T'>0$. Then there is a periodic Reeb orbit $(x,T')$ on $S$ with $x(0)=p$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, § 4.4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of periodic Reeb orbits: if `Qₖ` are periodic Reeb orbits on a strictly star-shaped
level with `Qₖ.x 0 → p` and `Qₖ.T → T' > 0`, then there is a periodic Reeb orbit through `p` with
period `T'`. -/
theorem exists_reebOrbit_of_tendsto {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (Q : ℕ → ReebOrbit H) (p : V n) (T' : ℝ) (hT' : 0 < T')
    (hp : Tendsto (fun k => (Q k).x 0) atTop (𝓝 p))
    (hT : Tendsto (fun k => (Q k).T) atTop (𝓝 T')) :
    ∃ P : ReebOrbit H, P.T = T' ∧ P.x 0 = p := by
  sorry

end FiniteEnergyPlane
