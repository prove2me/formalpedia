-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_uniform_hit_near_orbit
-- name    : FiniteEnergyPlane.exists_uniform_hit_near_orbit
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T12:29:25.180175+00:00
-- url     : https://prove2.me/theorems/138fff41-0b87-4970-ac85-9d264b8d19e3
-- title:
--   Uniform local hitting of a fast plane near its asymptotic orbit
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, with a $d\lambda_0$-compatible complex structure $J$ on $\xi$. Let $\tilde u = (a, u)$ be a fast finite-energy plane, nondegenerately asymptotic at $\infty$ to the periodic Reeb orbit $P = (x, T)$, and assume $\mu_{CZ}(P) \geq 3$. Then there are an open set $W \supseteq x(\mathbb{R})$ and a time $L > 0$ with the following property. Every Reeb trajectory $y$ with $y(0) \in W \setminus x(\mathbb{R})$ meets the surface $\mathrm{proj}(u(\mathbb{C})) \subset S$ at some time $t \in (0, L]$ and at some time $t \in [-L, 0)$.
--
--   Role: a uniform local version of Hryniewicz (2012), Lemma 6.9. Near the binding orbit $P$, every trajectory off $P$ meets the page $u(\mathbb{C})$ within a bounded time, both forward and backward.
--
--   Formalization Note: $S$ sits in $V\,1 = \mathbb{R}^4$, and `proj H` is the radial projection onto $S$, so the $S$-component of the plane is `fun z => proj H (u z)`. The hypotheses are the same as in `FiniteEnergyPlane.exists_hit_of_tendsto_orbit`: `IsFastPlane H J u`, `IsNondegenerateEnd H u cylInf P 1` (asymptotic to $P$ at $\infty$), and `P.IsCZAtLeast 3`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (Lemma 6.9); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 6.2; Hofer–Wysocki–Zehnder (Ann. of Math. 1998), § 5. Let `u`
be a fast finite-energy plane asymptotic to `P` at `∞`, where the Conley–Zehnder index of `P` is at
least `3`. There are an open set `W ⊇ x(ℝ)` and a time `L > 0` such that every Reeb trajectory `y`
with `y 0 ∈ W \ x(ℝ)` meets `proj H ∘ u` at some time in `(0, L]` and at some time in `[-L, 0)`. -/
theorem exists_uniform_hit_near_orbit (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧ ∃ L > 0, ∀ y : ℝ → V 1,
      IsReebTrajectory H y → y 0 ∈ W → y 0 ∉ Set.range P.x →
        (∃ t ∈ Set.Ioc 0 L, y t ∈ Set.range (fun z => proj H (u z))) ∧
        (∃ t ∈ Set.Ico (-L) 0, y t ∈ Set.range (fun z => proj H (u z))) := by
  sorry

end FiniteEnergyPlane
