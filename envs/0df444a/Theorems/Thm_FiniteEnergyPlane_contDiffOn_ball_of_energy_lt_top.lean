-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_ball_of_energy_lt_top
-- name    : FiniteEnergyPlane.contDiffOn_ball_of_energy_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T18:22:45.603133+00:00
-- url     : https://prove2.me/theorems/7c005a7e-65ea-4255-9845-fefdf753b499
-- title:
--   Regularity of a continuous finite-energy pseudoholomorphic map across a puncture
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $J$ a smooth almost complex structure on an open set $O\subseteq E$. Let $D\subset\mathbb{C}$ be the open unit disc and $v:D\to O$ continuous, with $v$ of class $C^\infty$ and $J$-holomorphic on $D\setminus\{0\}$ and
--   $$\int_{D\setminus\{0\}}\|Dv(z)\|^2\,dz<\infty.$$
--   Then $v$ is $C^\infty$ and $J$-holomorphic on all of $D$.
--
--   This is the regularity part of the removable singularity theorem: once a finite-energy puncture has a continuous extension, the extension is a smooth $J$-holomorphic map.
--
--   **Formalization Note** The energy is a lower integral in `ℝ≥0∞` of the squared operator norm of `fderiv ℝ v`. Continuity is `ContinuousOn v (ball 0 1)` and the values lie in `O` on the whole disc.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 4.8

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Regularity at a puncture (Zinger, *Notes on J-holomorphic maps*, Proposition 4.8). Let `J` be a
smooth almost complex structure on an open set `O ⊆ E`. A map `v` that is continuous on the unit disc
with values in `O`, smooth and `J`-holomorphic on the punctured disc, and of finite Dirichlet energy
`∫ ‖Dv‖²` on the punctured disc, is smooth and `J`-holomorphic on the whole disc. -/
theorem contDiffOn_ball_of_energy_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤) :
    ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v := by
  sorry

end FiniteEnergyPlane
