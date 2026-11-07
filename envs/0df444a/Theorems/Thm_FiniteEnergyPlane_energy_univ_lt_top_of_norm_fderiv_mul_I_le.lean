-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_univ_lt_top_of_norm_fderiv_mul_I_le
-- name    : FiniteEnergyPlane.energy_univ_lt_top_of_norm_fderiv_mul_I_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T17:20:37.71003+00:00
-- url     : https://prove2.me/theorems/d2e1f604-582e-486e-922e-0685ff9bfec9
-- title:
--   A J-holomorphic plane with bounded angular derivative has finite Hofer energy
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level in $V_n$ and $J$ a compatible complex structure on $\xi$. Let $u : \mathbb{C} \to V_n$ be smooth, avoid $0$ and be $\tilde J$-holomorphic, and suppose the projection $w = \mathrm{proj} \circ u$ to $S$ has bounded angular derivative: $\|Dw(z)(iz)\| \leq K$ for all $z$. Then the Hofer energy of $u$ on $\mathbb{C}$ is finite.
--
--   A criterion for finite energy in terms of the derivative in the circle direction only.
-- source:
--   H. Hofer, Invent. Math. 114 (1993), § 3; U. Hryniewicz, Trans. AMS 364 (2012), § 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A smooth `J̃`-holomorphic plane avoiding `0` whose projection to `S` has bounded angular
derivative, `‖D(proj ∘ u)(z)(i z)‖ ≤ K` for all `z`, has finite Hofer energy. -/
theorem energy_univ_lt_top_of_norm_fderiv_mul_I_le {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (K : ℝ)
    (hK : ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K) :
    energy H Set.univ u < ⊤ := by
  sorry

end FiniteEnergyPlane
