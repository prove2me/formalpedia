-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd
-- name    : FiniteEnergyPlane.exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T17:20:48.713202+00:00
-- url     : https://prove2.me/theorems/18687427-6927-499c-9606-a819f78e4df0
-- title:
--   Bounded angular derivative for a map converging exponentially to a trivial cylinder at infinity
-- statement:
--   Let $P = (x, T)$ be a periodic Reeb orbit on a strictly star-shaped level $S$. Let $u : \mathbb{C} \to V_n$ be such that $w = \mathrm{proj} \circ u$ is $C^1$ and $u$ converges to the trivial cylinder over $P$ exponentially fast in $C^\infty$ in the cylindrical coordinates at $\infty$. Then $z \mapsto \|Dw(z)(iz)\|$ is bounded on $\mathbb{C}$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.11

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A map with `C¹` projection to `S` that converges to the trivial cylinder over `P` exponentially
fast in `C^∞` at `∞` has bounded angular derivative: `‖D(proj ∘ u)(z)(i z)‖` is bounded on `ℂ`. -/
theorem exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u : ℂ → V n)
    (hw : ContDiff ℝ 1 (fun z => proj H (u z))) (P : ReebOrbit H) (b : ℝ) (hb : 0 < b)
    (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b) :
    ∃ K : ℝ, ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K := by
  sorry

end FiniteEnergyPlane
