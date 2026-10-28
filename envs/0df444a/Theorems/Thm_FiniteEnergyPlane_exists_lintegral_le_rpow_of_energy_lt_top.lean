-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_lintegral_le_rpow_of_energy_lt_top
-- name    : FiniteEnergyPlane.exists_lintegral_le_rpow_of_energy_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:14:34.169608+00:00
-- url     : https://prove2.me/theorems/22a2492e-0357-4d8b-8849-c73691a98408
-- title:
--   Energy decay on small discs about a removable puncture
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $J$ a smooth almost complex structure on an open set $O\subseteq E$. Let $D\subset\mathbb{C}$ be the open unit disc and $v:D\to O$ continuous, with $v$ of class $C^\infty$ and $J$-holomorphic on $D\setminus\{0\}$,
--   $$\int_{D\setminus\{0\}}\|Dv(z)\|^2\,dz<\infty,$$
--   and $|z|\,\|Dv(z)\|\le C$ for $0<|z|<r_1$. Then there are $\mu>0$, $r>0$ and $K$ such that
--   $$\int_{|z|<s}\|Dv(z)\|^2\,dz\le K\,s^{2\mu}\qquad\text{for all }0<s\le r .$$
--
--   The energy of a pseudoholomorphic map on small discs about a removable puncture decays like a positive power of the radius. This is the quantitative input for the regularity of the extension across the puncture.
--
--   **Formalization Note** The energy on the disc of radius `s` is the lower integral `∫⁻ z in ball 0 s, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2)` (the value of `fderiv` at the single point `0` does not affect it). The bound on `|z| ‖Dv(z)‖` is the hypothesis `hG`.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Corollary 4.10

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Energy decay at a puncture (Zinger, *Notes on J-holomorphic maps*, Corollary 4.10). Let `J` be
a smooth almost complex structure on an open set `O ⊆ E`, and let `v` be continuous on the unit disc
with values in `O`, smooth and `J`-holomorphic on the punctured disc, of finite Dirichlet energy, and
with `|z| ‖Dv(z)‖` bounded near `0`. Then there are `μ > 0`, `r > 0` and `K` with
`∫_{|z| < s} ‖Dv‖² ≤ K s^{2μ}` for all `0 < s ≤ r`. -/
theorem exists_lintegral_le_rpow_of_energy_lt_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ v z‖ ≤ C) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) ≤ ENNReal.ofReal (K * s ^ (2 * μ)) := by
  sorry

end FiniteEnergyPlane
