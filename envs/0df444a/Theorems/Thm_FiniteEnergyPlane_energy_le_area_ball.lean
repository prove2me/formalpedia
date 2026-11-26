-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_le_area_ball
-- name    : FiniteEnergyPlane.energy_le_area_ball
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:09:23.720716+00:00
-- url     : https://prove2.me/theorems/7aa6c63a-d6dc-5e5d-8f49-a6cd548c3b7a
-- title:
--   The energy of a disk with boundary on an embedded disk is at most the positive area
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $e$ embed $B_\rho$, $\rho>1$, into $S$, let $r<\rho$, and let $u$ be an embedded $\tilde J$-holomorphic disk with boundary loop in $e(\overline{B_r})$, winding once around $e(z_0)$. Then
--   $$E(u)\le\int_{B_r}\max\big(\omega_0(\partial_se,\partial_te),0\big)\,ds\,dt ,$$
--   where $E$ is Hofer's energy.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. The bound is uniform over all such disks and all compatible $J$, with no hypothesis on the zeros or leaves of the characteristic field.
--
--   **Formalization Note** The disk is `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`. The source has the total area $\int|d\lambda|$ instead of the positive part, and an additional assertion that is not stated here.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Lemma 33

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Lemma 33 (the energy bound). Let `e` embed the disk of radius `ρ` into `S`, and let `r < ρ`. An
embedded `J̃`-holomorphic disk with boundary loop in `e({|z| ≤ r})` has Hofer energy at most the positive
part of the `dλ₀`-area of `e` on the disk of radius `r`. -/
theorem energy_le_area_ball (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (r : ℝ) (hrρ : r < ρ) (z₀ : ℂ) (u : ℂ → V 1)
    (hu : IsEmbeddedHoloDisk H J e z₀ (closedBall 0 r) u) :
    energy H (ball 0 1) u ≤ ∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal (omega0 (ds e z) (dt e z)) := by
  sorry

end FiniteEnergyPlane
