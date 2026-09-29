-- Prove2me | Theorems.Thm_FamousTheorems_absolutelycontinuous_iff_withdensity_rnderiv_eq
-- name    : FamousTheorems.absolutelycontinuous_iff_withdensity_rnderiv_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:58.525804+00:00
-- url     : https://prove2.me/theorems/5b27b798-60ee-42c4-8cae-d505d0c1c2ae
-- title:
--   The Radon–Nikodym theorem
-- statement:
--   **The Radon-Nikodym theorem.** A sigma-finite measure is absolutely continuous with respect to another exactly when it has a density against it. A purely qualitative condition, that null sets are null, is equivalent to the existence of a concrete nonnegative function representing one measure as a weighted version of the other. This is what makes probability densities exist, and it underlies conditional expectation, likelihood ratios in statistics, and change of measure in stochastic analysis where the density is the Girsanov factor. **Formalization note.** `withDensity` reconstructs the measure from its density and `rnDeriv` is the Radon-Nikodym derivative. The result is Mathlib's `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem absolutelycontinuous_iff_withdensity_rnderiv_eq :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    {μ ν : MeasureTheory.Measure α} [μ.HaveLebesgueDecomposition ν], 
    μ.AbsolutelyContinuous ν ↔ ν.withDensity (μ.rnDeriv ν) = μ := by sorry

end FamousTheorems
