-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:54:25.382196+00:00
-- url     : https://prove2.me/theorems/2b010b40-909f-4a8c-aa49-9caf5d12cf14
-- title:
--   A plane asymptotic to an orbit stays away from its value at the origin
-- statement:
--   Let $H$ be a strictly star-shaped level function on $V_n$, $P$ a Reeb orbit, and $u : \mathbb{C} \to V_n$ continuous, injective, avoiding $0$, and asymptotic to $P$ at $\infty$ in the sense of `IsNondegenerateEnd H u cylInf P 1`. For every $\rho > 0$ there is $\eta > 0$ such that for all $z$ with $|z| \ge \rho$,
--   $$\eta \le |a_H(u(z)) - a_H(u(0))| + \|\mathrm{proj}_H(u(z)) - \mathrm{proj}_H(u(0))\|.$$
--
--   **Role.** A uniform separation of $u(0)$ from the part of the plane outside a ball, measured in the coordinates of the symplectization. These are the coordinates used by `IsCylCloseTo`.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- An injective continuous plane avoiding `0` and asymptotic to a Reeb orbit at `∞` stays away from
its value at `0` in the symplectization coordinates, outside any ball around `0`. -/
theorem exists_pos_le_aCoord_add_proj_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n) (hu0 : ∀ z, u z ≠ 0)
    (huc : Continuous u) (hui : Function.Injective u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ η > 0, ∀ z, ρ ≤ ‖z‖ →
      η ≤ |aCoord H (u z) - aCoord H (u 0)| + ‖proj H (u z) - proj H (u 0)‖ := by
  sorry

end FiniteEnergyPlane
