-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebOrbit_families_finite
-- name    : FiniteEnergyPlane.exists_reebOrbit_families_finite
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:23:27.975626+00:00
-- url     : https://prove2.me/theorems/5961051f-2ed5-46e9-b98b-b96646e5e5c7
-- title:
--   Finitely many families of nondegenerate Reeb orbits below a period bound
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $T\in\mathbb{R}$, and suppose every periodic Reeb orbit of period at most $T$ is nondegenerate. Then there are finitely many periodic orbits $Q_1=(x_1,T_1),\dots,Q_N=(x_N,T_N)$ with $T_i\le T$ and a number $\delta>0$ such that
--   1. every periodic orbit $(x,T')$ with $T'\le T$ is a time shift of some $Q_i$ with the same period: $T'=T_i$ and $x(\tau)=x_i(\tau+c)$ for some $c$;
--   2. for $i\neq j$ and all phases $c,c'$, $\sup_t|x_i(T_it+c)-x_j(T_jt+c')|\ge\delta$.
--
--   **Formalization Note** Part 2 is stated as: there is $t$ with $\delta\le\|x_i(T_it+c)-x_j(T_jt+c')\|$ (sup norm on $\mathbb{R}^{2n+2}$).
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 2, formula (6), and Section 4.4

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `S = H⁻¹(1)` be a strictly star-shaped level and `T > 0`, and suppose every periodic Reeb
orbit of period at most `T` is nondegenerate. Then these orbits form finitely many families: there
are orbits `Q₁, …, Q_N` of period at most `T` such that every periodic orbit of period at most `T`
is a time shift of some `Qᵢ` with the same period, and the normalized loops of distinct families
`t ↦ Qᵢ.x(Tᵢ t + c)` and `t ↦ Qⱼ.x(Tⱼ t + c')` stay `C⁰`-distance at least `δ > 0` apart for all
phases `c, c'`. (Hryniewicz, Trans. AMS 2012, (6) and § 4.4: finiteness of the orbits of bounded
period.) -/
theorem exists_reebOrbit_families_finite {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (T : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ T → Q.IsNondegenerate) :
    ∃ (N : ℕ) (Q : Fin N → ReebOrbit H) (δ : ℝ), 0 < δ ∧ (∀ i, (Q i).T ≤ T) ∧
      (∀ R : ReebOrbit H, R.T ≤ T →
        ∃ i, (Q i).T = R.T ∧ ∃ c : ℝ, ∀ τ : ℝ, R.x τ = (Q i).x (τ + c)) ∧
      ∀ i j, i ≠ j → ∀ c c' : ℝ, ∃ t : ℝ,
        δ ≤ ‖(Q i).x ((Q i).T * t + c) - (Q j).x ((Q j).T * t + c')‖ := by
  sorry

end FiniteEnergyPlane
